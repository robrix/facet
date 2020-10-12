{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Parser
( runFacet
, Facet(..)
, module'
, decl
, type'
, expr
, whole
) where

import           Control.Applicative (Alternative(..))
import           Control.Carrier.Reader
import           Control.Selective
import           Data.Bool (bool)
import           Data.Char (isSpace)
import qualified Data.CharSet as CharSet
import qualified Data.CharSet.Unicode as Unicode
import           Data.Coerce (Coercible, coerce)
import           Data.Foldable (foldl')
import qualified Data.HashSet as HashSet
import           Data.List (elemIndex)
import qualified Data.List.NonEmpty as NE
import           Data.Text (Text, pack)
import qualified Facet.Name as N
import           Facet.Parser.Table as Op
import qualified Facet.Surface.Decl as D
import qualified Facet.Surface.Expr as E
import qualified Facet.Surface.Module as M
import qualified Facet.Surface.Pattern as P
import qualified Facet.Surface.Type as T
import qualified Facet.Syntax as S
import           Prelude hiding (lines, null, product, span)
import           Text.Parser.Char
import           Text.Parser.Combinators
import           Text.Parser.Position
import           Text.Parser.Token
import           Text.Parser.Token.Highlight as Highlight
import           Text.Parser.Token.Style

-- case
-- : (x : a) -> (f : a -> b) -> b
-- { f x }

-- TODO:
-- list literals
-- numeric literals
-- forcing nullary computations

runFacet :: [N.UName] -> Facet m a -> m a
runFacet env (Facet m) = m env

bind :: Coercible t N.UName => t -> (N.UName -> Facet m a) -> Facet m a
bind n b = Facet $ \ env -> let n' = coerce n in runFacet (n':env) (b n')

resolve :: Coercible t N.UName => t -> [N.UName] -> (Either t N.Index)
resolve n = maybe (Left n) (Right . N.Index) . elemIndex @N.UName (coerce n)

env :: Applicative m => Facet m [N.UName]
env = Facet pure

newtype Facet m a = Facet ([N.UName] -> m a)
  deriving (Alternative, Applicative, Functor, Monad, MonadFail) via ReaderC [N.UName] m

instance Selective m => Selective (Facet m) where
  select f a = Facet $ \ env -> select (runFacet env f) (runFacet env a)

instance Parsing p => Parsing (Facet p) where
  try (Facet m) = Facet $ \ env -> try (m env)
  Facet m <?> l = Facet $ \ env -> m env <?> l
  skipMany (Facet m) = Facet $ \ env -> skipMany (m env)
  unexpected = lift . unexpected
  eof = lift eof
  notFollowedBy (Facet m) = Facet $ \ env -> notFollowedBy (m env)

instance CharParsing p => CharParsing (Facet p) where
  satisfy = lift . satisfy
  char    = lift . char
  notChar = lift . notChar
  anyChar = lift anyChar
  string  = lift . string
  text    = lift . text

instance TokenParsing m => TokenParsing (Facet m) where
  someSpace = buildSomeSpaceParser (skipSome (satisfy isSpace)) emptyCommentStyle{ _commentLine = "#" }

instance PositionParsing p => PositionParsing (Facet p) where
  position = lift position

lift :: p a -> Facet p a
lift = Facet . const


whole :: TokenParsing p => p a -> p a
whole p = whiteSpace *> p <* eof


-- Modules

module' :: (Monad p, PositionParsing p) => Facet p (M.Module Span)
module' = mk <$> spanned ((,) <$> mname <* colon <* symbol "Module" <*> braces (many decl))
  where
  mk (s, (n, ds)) = M.Module s n ds

decl :: (Monad p, PositionParsing p) => Facet p (M.Def Span)
decl = mk <$> spanned ((,) <$> dname <* colon <*> sig)
  where
  mk (s, (n, b)) = M.Def s n b


-- Declarations

sigTable :: (Monad p, PositionParsing p) => Table (Facet p) (D.Decl Span)
sigTable =
  [ [ Op.Operator (forAll (D.:=>)) ]
  , [ Op.Operator binder ]
  ]

sig :: (Monad p, PositionParsing p) => Facet p (D.Decl Span)
sig = build sigTable (const (settingSpan ((D.:=) <$> monotype <*> comp))) -- FIXME: parse type declarations too

binder :: (Monad p, PositionParsing p) => OperatorParser (Facet p) (D.Decl Span)
binder self _ = do
  ((start, i), t) <- nesting $ (,) <$> try ((,) <$> position <* symbolic '(' <*> varPattern ename) <* colon <*> type' <* symbolic ')'
  bindVarPattern i $ \ v -> mk start (v S.::: t) <$ arrow <*> self <*> position
  where
  mk start t b end = setSpan (Span start end) $ t D.:-> b


-- Types

typeTable :: (Monad p, PositionParsing p) => Table (Facet p) (T.Type Span)
typeTable = [ Op.Operator (forAll (T.:=>)) ] : monotypeTable

monotypeTable :: (Monad p, PositionParsing p) => Table (Facet p) (T.Type Span)
monotypeTable =
  [ [ Infix R (pack "->") (\ s -> fmap (setSpan s) . (T.:->)) ]
  , [ Infix L mempty (\ s -> fmap (setSpan s) . (T.:$)) ]
  , [ -- FIXME: we should treat these as globals.
      Atom (T.Type <$ token (string "Type"))
    , Atom (T.Void <$ token (string "Void"))
    , Atom (T.Unit <$ token (string "Unit"))
    , Atom tvar
    ]
  ]

forAll
  :: (Monad p, PositionParsing p, Spanned res)
  => ((N.UName S.::: T.Type Span) -> res -> res)
  -> OperatorParser (Facet p) res
forAll mk self _ = do
  start <- position
  (names, ty) <- braces ((,) <$> commaSep1 tname <* colon <*> type')
  arrow *> foldr (loop start ty) self names
  where
  loop start ty i rest = bind i $ \ v -> mk' start (v S.::: ty) <$> rest <*> position
  mk' start t b end = setSpan (Span start end) $ mk t b

type' :: (Monad p, PositionParsing p) => Facet p (T.Type Span)
type' = build typeTable (terminate parens (parseOperator (Infix L (pack ",") (\ s -> fmap (setSpan s) . (T.:*)))))

monotype :: (Monad p, PositionParsing p) => Facet p (T.Type Span)
monotype = build monotypeTable (terminate parens (parseOperator (Infix L (pack ",") (\ s -> fmap (setSpan s) . (T.:*)))))

tvar :: (Monad p, PositionParsing p) => Facet p (T.Type Span)
tvar = token (settingSpan (runUnspaced (fmap (either (T.Free . N.T) (T.Bound)) . resolve <$> tname <*> Unspaced env <?> "variable")))


-- Expressions

exprTable :: (Monad p, PositionParsing p) => Table (Facet p) (E.Expr Span)
exprTable =
  [ [ Infix L mempty (\ s -> fmap (setSpan s) . (E.:$)) ]
  , [ Atom comp
    , Atom (E.Hole <$> hname)
    , Atom evar
    ]
  ]

expr :: (Monad p, PositionParsing p) => Facet p (E.Expr Span)
expr = build exprTable (terminate parens (parseOperator (Infix L (pack ",") (\ s -> fmap (setSpan s) . (E.:*)))))

comp :: (Monad p, PositionParsing p) => Facet p (E.Expr Span)
comp = settingSpan (braces (E.Comp <$> clauses))
  where
  clauses
    =   sepBy1 clause comma
    <|> pure <$> body
    <|> pure []

clause :: (Monad p, PositionParsing p) => Facet p (E.Clause Span)
clause = (try (some ((,) <$> position <*> pattern) <* arrow) >>= foldr go body) <?> "clause"
  where
  go (start, p) rest = bindPattern p $ \ p' -> do
    c <- E.Clause p' <$> rest
    end <- position
    pure $ setSpan (Span start end) c

body :: (Monad p, PositionParsing p) => Facet p (E.Clause Span)
body = E.Body <$> expr

evar :: (Monad p, PositionParsing p) => Facet p (E.Expr Span)
evar
  =   token (settingSpan (runUnspaced (fmap (either (E.Free . N.E) E.Bound) . resolve <$> ename <*> Unspaced env <?> "variable")))
  <|> try (token (settingSpan (runUnspaced (E.Free . N.O <$> Unspaced (parens oname))))) -- FIXME: would be better to commit once we see a placeholder, but try doesn’t really let us express that


-- Patterns

bindPattern :: PositionParsing p => P.Pattern N.EName -> (P.Pattern N.UName -> Facet p a) -> Facet p a
bindPattern p f = case p of
  P.Wildcard -> bind (N.EName N.__) (const (f P.Wildcard))
  P.Var n    -> bind n              (f . P.Var)
  P.Tuple ps -> foldr (\ p k ps -> bindPattern p $ \ p' -> k (ps . (p':))) (f . P.Tuple . ($ [])) ps id
  P.Loc _ p  -> bindPattern p f

bindVarPattern :: Maybe N.EName -> (N.UName -> Facet p res) -> Facet p res
bindVarPattern Nothing  = bind (N.EName N.__)
bindVarPattern (Just n) = bind n


varPattern :: (Monad p, TokenParsing p) => p name -> p (Maybe name)
varPattern n = Just <$> n <|> Nothing <$ wildcard


wildcard :: (Monad p, TokenParsing p) => p ()
wildcard = reserve enameStyle "_"

-- FIXME: patterns
pattern :: (Monad p, PositionParsing p) => p (P.Pattern N.EName)
pattern = settingSpan
  $   P.Var      <$> ename
  <|> P.Wildcard <$  wildcard
  <|> P.Tuple    <$> parens (commaSep pattern)
  <?> "pattern"


-- Names

ename :: (Monad p, TokenParsing p) => p N.EName
ename  = ident enameStyle

oname :: (Monad p, TokenParsing p) => p N.Op
oname
  =   postOrIn <$ place <*> comp <*> option False (True <$ place)
  <|> try (outOrPre <$> comp <* place) <*> optional comp
  where
  place = wildcard
  comp = ident onameStyle
  outOrPre s e = maybe (N.Prefix s) (N.Outfix s) e
  -- FIXME: how should we specify associativity?
  postOrIn c = bool (N.Postfix c) (N.Infix N.N c)

_onameN :: (Monad p, TokenParsing p) => p N.OpN
_onameN
  =   postOrIn <$ place <*> sepByNonEmpty comp place <*> option False (True <$ place)
  <|> try (uncurry . outOrPre <$> comp <* place) <*> ((,) <$> sepBy1 comp place <*> option False (True <$ place) <|> pure ([], True))
  where
  place = wildcard
  comp = ident onameStyle
  outOrPre c cs = bool (N.OutfixN c (init cs) (last cs)) (N.PrefixN c cs)
  -- FIXME: how should we specify associativity?
  postOrIn cs = bool (N.PostfixN (NE.init cs) (NE.last cs)) (N.InfixN N.N cs)

hname :: (Monad p, TokenParsing p) => p Text
hname = ident hnameStyle

tname :: (Monad p, TokenParsing p) => p N.TName
tname = ident tnameStyle

dname :: (Monad p, TokenParsing p) => p N.DName
dname  = N.E <$> ename <|> N.T <$> tname <|> N.O <$> oname

mname :: (Monad p, TokenParsing p) => p N.MName
mname = token (runUnspaced (foldl' (N.:.) . N.MName <$> comp <* dot <*> sepBy comp dot))
  where
  comp = ident tnameStyle

reserved :: HashSet.HashSet String
reserved = HashSet.singleton "_"

nameChar :: CharParsing p => p Char
nameChar = alphaNum <|> char '_'

opChar :: CharParsing p => p Char
opChar = oneOfSet (CharSet.difference (Unicode.punctuation <> Unicode.symbol) (CharSet.fromList "(){}"))

enameStyle :: CharParsing p => IdentifierStyle p
enameStyle = IdentifierStyle
  "name"
  (lower <|> char '_')
  nameChar
  reserved
  Identifier
  ReservedIdentifier

onameStyle :: CharParsing p => IdentifierStyle p
onameStyle = IdentifierStyle
  "operator"
  opChar
  opChar
  mempty
  Highlight.Operator
  ReservedOperator

tnameStyle :: CharParsing p => IdentifierStyle p
tnameStyle = IdentifierStyle
  "type name"
  upper
  nameChar
  reserved
  Identifier
  ReservedIdentifier

hnameStyle :: CharParsing p => IdentifierStyle p
hnameStyle = IdentifierStyle
  "hole name"
  (char '?')
  nameChar
  reserved
  Identifier
  ReservedIdentifier

arrow :: TokenParsing p => p String
arrow = symbol "->"
