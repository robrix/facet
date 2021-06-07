{-# LANGUAGE UndecidableInstances #-}
module Facet.Parser
( whole
, makeOperator
, module'
, moduleHeader
, decl
, type'
, expr
, mname
, runFacet
, Facet(..)
) where

import           Control.Algebra ((:+:))
import           Control.Applicative (Alternative(..), (<**>))
import qualified Control.Carrier.Reader as C
import qualified Control.Carrier.State.Strict as C
import qualified Control.Carrier.Writer.Strict as C
import           Control.Effect.Reader
import           Control.Effect.State
import           Control.Effect.Writer
import           Control.Monad.Fix
import           Control.Monad.Trans.Class
import           Data.Bool (bool)
import           Data.Char (isSpace)
import qualified Data.CharSet as CharSet
import qualified Data.CharSet.Unicode as Unicode
import           Data.Foldable (foldl')
import           Data.Functor (void)
import qualified Data.HashSet as HashSet
import qualified Data.List.NonEmpty as NE
import           Data.Text (pack)
import           Facet.Effect.Parser
import qualified Facet.Name as N
import           Facet.Parser.Table as Op
import           Facet.Snoc
import           Facet.Span
import qualified Facet.Surface as S
import           Facet.Syntax
import           Prelude hiding (lines, null, product, span)
import           Text.Parser.Char
import           Text.Parser.Combinators
import           Text.Parser.Token
import           Text.Parser.Token.Highlight as Highlight

-- TODO:
-- list literals
-- numeric literals

-- FIXME: allow operators to be introduced and scoped locally
-- FIXME: we can’t parse without knowing operators defined elsewhere
-- FIXME: parse {A} as a synonym for Unit -> A. Better yet, implement mixfix type operators & type synonyms, and define it as a synonym in Data.Unit.

whole :: TokenParsing p => p a -> p a
whole p = whiteSpace *> p <* eof


makeOperator :: (N.MName, N.Op, N.Assoc) -> Operator (S.Ann S.Expr)
makeOperator (name, op, assoc) = (op, assoc, nary (N.toQ (name N.:.: N.O op)))
  where
  nary name es = foldl' (S.annBinary S.App) (S.Ann (S.ann (head es)) Nil (S.Var name)) es


-- Modules

module' :: (Has Parser sig p, Has (State [Operator (S.Ann S.Expr)]) sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann S.Module)
module' = anned $ do
  (name, imports) <- moduleHeader
  decls <- C.runReader name (runReaderC (many decl))
  ops <- get @[Operator (S.Ann S.Expr)]
  pure $ S.Module name imports (map (\ (op, assoc, _) -> (op, assoc)) ops) decls

moduleHeader :: (Has Parser sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => p (N.MName, [S.Ann S.Import])
moduleHeader = (,) <$ reserve dnameStyle "module" <*> mname <* colon <* symbol "Module" <*> many import'


-- Declarations

import' :: (Has Parser sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann S.Import)
import' = anned $ S.Import <$ reserve dnameStyle "import" <*> mname

decl :: (Has Parser sig p, Has (Reader N.MName) sig p, Has (State [Operator (S.Ann S.Expr)]) sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann (N.Name, S.Ann S.Def))
decl = choice
  [ termDecl
  , dataDecl
  , interfaceDecl
  ]

-- FIXME: operators aren’t available until after their declarations have been parsed.
-- FIXME: parse operator declarations in datatypes.
-- FIXME: parse operator declarations in interfaces.
termDecl :: (Has Parser sig p, Has (Reader N.MName) sig p, Has (State [Operator (S.Ann S.Expr)]) sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann (N.Name, S.Ann S.Def))
termDecl = anned $ do
  name <- dename
  case name of
    N.O op -> do
      assoc <- case op of
        N.Infix _ -> option N.N $ brackets $ choice
          [ N.N <$ symbol "non-assoc"
          , N.L <$ symbol "left-assoc"
          , N.R <$ symbol "right-assoc"
          , N.A <$ symbol "assoc"
          ]
        _ -> pure N.N
      mname <- ask
      modify (makeOperator (mname, op, assoc) :)
    _      -> pure ()
  decl <- anned $ colon *> typeSig ename <**> (S.TermDef <$> body)
  pure (name, decl)

body :: (Has Parser sig p, Has (State [Operator (S.Ann S.Expr)]) sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann S.Expr)
-- NB: We parse sepBy1 and the empty case separately so that it doesn’t succeed at matching 0 clauses and then expect a closing brace when it sees a nullary computation
body = fmap (either S.out id) <$> anned (braces (Right . S.Lam <$> sepBy1 clause comma <|> Left <$> expr <|> pure (Right (S.Lam []))))


dataDecl :: (Has Parser sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann (N.Name, S.Ann S.Def))
dataDecl = anned $ (,) <$ reserve dnameStyle "data" <*> tname <* colon <*> anned (kindSig tname <**> (S.DataDef <$> braces (commaSep con)))

interfaceDecl :: (Has Parser sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann (N.Name, S.Ann S.Def))
interfaceDecl = anned $ (,) <$ reserve dnameStyle "interface" <*> tname <* colon <*> anned (kindSig tname <**> (S.InterfaceDef <$> braces (commaSep con)))

con :: (Has Parser sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann (N.Name ::: S.Ann S.Type))
con = anned ((:::) <$> dename <* colon <*> rec)
  where
  rec = choice [ forAll rec, type' ]


kindSig
  :: (Has Parser sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p)
  => p N.Name -- ^ a parser for names occurring in explicit (parenthesized) bindings
  -> p (S.Ann S.Kind)
kindSig name = choice [ kindArrow name (kindSig name), kind ]

typeSig
  :: (Has Parser sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p)
  => p N.Name -- ^ a parser for names occurring in explicit (parenthesized) bindings
  -> p (S.Ann S.Type)
typeSig name = choice [ forAll (typeSig name), bindArrow name (typeSig name), type' ]


-- Types

kind :: (Has Parser sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann S.Kind)
kind = choice
  [ token (anned (S.KType      <$ string "Type"))
  , token (anned (S.KInterface <$ string "Interface"))
  ]

kindArrow :: (Has Parser sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => p N.Name -> p (S.Ann S.Kind) -> p (S.Ann S.Kind)
kindArrow name k = anned (try (S.KArrow . Just <$ lparen <*> (name <|> N.__ <$ wildcard) <* colon) <*> kind <* rparen <* arrow <*> k)


-- FIXME: kind ascriptions
monotypeTable :: (Has Parser sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => Table p (S.Ann S.Type)
monotypeTable =
  [ [ functionType ]
  , [ retType ]
  , [ parseOperator (N.Infix mempty, N.L, foldl1 (S.annBinary S.TApp)) ]
  , [ -- FIXME: we should treat these as globals.
      atom (token (anned (S.TString    <$ string "String")))
      -- FIXME: holes in types
    , atom tvar
    ]
  ]


type' :: (Has Parser sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann S.Type)
type' = monotype


forAll :: (Has Parser sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann S.Type) -> p (S.Ann S.Type)
forAll k = make <$> anned (try (((,,) <$ lbrace <*> commaSep1 ((,) <$> position <*> tname) <* colon) <*> kind <* rbrace <* arrow) <*> k)
  where
  make (S.Ann s cs (ns, t, b)) = S.Ann s cs (S.out (foldr (\ (p, n) b -> S.Ann (Span p (end s)) Nil (S.TForAll n t b)) b ns))

bindArrow :: (Has Parser sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => p N.Name -> p (S.Ann S.Type) -> p (S.Ann S.Type)
bindArrow name k = anned (try (S.TArrow . Just <$ lparen <*> (name <|> N.__ <$ wildcard) <* colon) <*> optional mul <*> type' <* rparen <* arrow <*> k)

functionType :: (Has Parser sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann S.Type) -> p (S.Ann S.Type) -> p (S.Ann S.Type)
functionType self next = anned (try (S.TArrow Nothing <$> optional mul <*> next <* arrow) <*> self) <|> next

mul :: TokenParsing p => p S.Mul
mul = choice [ S.Zero <$ token (char '0'), S.One <$ token (char '1') ]


retType :: (Has Parser sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann S.Type) -> p (S.Ann S.Type) -> p (S.Ann S.Type)
retType _ next = mk <$> anned ((,) <$> optional signature <*> next)
  where
  mk (S.Ann s c (sig, _T)) = maybe id (\ sig -> S.Ann s c . S.TComp sig) sig _T


-- FIXME: support type operators
monotype :: (Has Parser sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann S.Type)
monotype = build monotypeTable $ parens type'

tvar :: (Has Parser sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann S.Type)
tvar = anned (S.TVar <$> qname tname)


signature :: (Has Parser sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => p [S.Ann S.Interface]
signature = brackets (commaSep delta) <?> "signature"
  where
  delta = anned $ S.Interface <$> head <*> (fromList <$> many type')
  head = fmap mkHead <$> token (anned (runUnspaced (sepByNonEmpty comp dot)))
  mkHead cs = fromList (NE.init cs) N.:. NE.last cs
  comp = ident tnameStyle


-- Expressions

exprTable :: (Has Parser sig p, Has (State [Operator (S.Ann S.Expr)]) sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => Table p (S.Ann S.Expr)
exprTable =
  -- FIXME: parse this as a unary operator or something
  -- FIXME: better yet, generalize operators to allow different syntactic types on either side (following the associativity)
  [ [ ascription ]
  , [ parseOperator (N.Infix mempty, N.L, foldl1 (S.annBinary S.App)) ]
  , [ atom thunk, atom hole, atom evar, atom (token (anned (runUnspaced (S.String <$> stringLiteral)))) ]
  ]

expr :: (Has Parser sig p, Has (State [Operator (S.Ann S.Expr)]) sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann S.Expr)
expr = do
  ops <- get
  let rec = build (map parseOperator ops:exprTable) $ parens rec
  rec

ascription :: (Has Parser sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann S.Expr) -> p (S.Ann S.Expr) -> p (S.Ann S.Expr)
ascription _self next = anned (S.As <$> try (next <* colon) <*> type') <|> next

thunk :: (Has Parser sig p, Has (State [Operator (S.Ann S.Expr)]) sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann S.Expr)
-- NB: We parse sepBy1 and the empty case separately so that it doesn’t succeed at matching 0 clauses and then expect a closing brace when it sees a nullary computation
thunk = anned (braces (S.Lam <$> sepBy1 clause comma <|> {-S.Thunk <$> expr <|>-} pure (S.Lam [])))

clause :: (Has Parser sig p, Has (State [Operator (S.Ann S.Expr)]) sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => p S.Clause
clause = S.Clause <$> try (compPattern <* arrow) <*> expr <?> "clause"

evar :: (Has Parser sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann S.Expr)
evar = choice
  [ token (anned (runUnspaced (S.Var <$> try ((N.:.) . fromList <$> many (comp <* dot) <*> ename))))
    -- FIXME: would be better to commit once we see a placeholder, but try doesn’t really let us express that
  , try (anned (parens (S.Var <$> qname (N.O <$> oname))))
  ]
  where
  comp = ident tnameStyle

hole :: (Has Parser sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann S.Expr)
hole = token (anned (runUnspaced (S.Hole <$> ident hnameStyle)))
  where
  hnameStyle = IdentifierStyle "hole name" (char '?') nameChar reserved Identifier ReservedIdentifier


-- Patterns

wildcard :: (Monad p, TokenParsing p) => p ()
wildcard = reserve enameStyle "_"

valuePattern :: (Has Parser sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann S.ValPattern)
valuePattern = choice
  [ token (anned (runUnspaced (S.PVar <$> ename <?> "variable")))
  , anned (S.PWildcard <$  wildcard)
  , try (parens (anned (S.PCon <$> qname ename <*> many valuePattern)))
  ] <?> "pattern"

compPattern :: (Has Parser sig p, Has (Writer (Snoc (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann S.Pattern)
compPattern = choice
  [ anned (S.PVal <$> valuePattern)
  , anned (S.PEff <$> try (brackets (anned (S.POp <$> qname ename <*> many valuePattern <* symbolic ';' <*> valuePattern))))
  ] <?> "pattern"


-- Names

ename :: (Monad p, TokenParsing p) => p N.Name
ename  = ident enameStyle

oname :: (Monad p, TokenParsing p) => p N.Op
oname = choice
  [ postOrIn <$ place <*> comp <*> option False (True <$ place)
  , try (outOrPre <$> comp <* place) <*> optional comp
  ]
  where
  place = wildcard
  comp = ident onameStyle
  outOrPre s e = maybe (N.Prefix s) (N.Outfix s) e
  postOrIn c = bool (N.Postfix c) (N.Infix c)

_onameN :: (Monad p, TokenParsing p) => p N.OpN
_onameN = choice
  [ postOrIn <$ place <*> sepByNonEmpty comp place <*> option False (True <$ place)
  , try (uncurry . outOrPre <$> comp <* place) <*> ((,) <$> sepBy1 comp place <*> option False (True <$ place) <|> pure ([], True))
  ]
  where
  place = wildcard
  comp = ident onameStyle
  outOrPre c cs = bool (N.OutfixN c (init cs) (last cs)) (N.PrefixN c cs)
  postOrIn cs = bool (N.PostfixN (NE.init cs) (NE.last cs)) (N.InfixN cs)

tname :: (Monad p, TokenParsing p) => p N.Name
tname = ident tnameStyle

dename :: (Monad p, TokenParsing p) => p N.Name
dename = N.U <$> ident dnameStyle <|> N.O <$> oname

mname :: (Monad p, TokenParsing p) => p N.MName
mname = token (runUnspaced (fromList <$> sepBy1 comp dot))
  where
  comp = ident tnameStyle

qname :: (Has Parser sig p, TokenParsing p) => p N.Name -> p N.QName
qname name = token (runUnspaced (try (fmap N.toQ . (N.:.:) <$> mname <*> Unspaced name) <|> (Nil N.:.) <$> Unspaced name)) <?> "name"


reserved :: HashSet.HashSet String
reserved = HashSet.singleton "_"

declarationReserved :: HashSet.HashSet String
declarationReserved = HashSet.fromList ["_", "data", "import", "interface", "module"]

nameChar :: CharParsing p => p Char
nameChar = alphaNum <|> char '_'

opChar :: CharParsing p => p Char
opChar = oneOfSet (CharSet.difference (Unicode.punctuation <> Unicode.symbol) (CharSet.fromList "(){}"))

dnameStyle :: CharParsing p => IdentifierStyle p
dnameStyle = IdentifierStyle "declaration name" (lower <|> char '_') nameChar declarationReserved Identifier ReservedIdentifier

enameStyle :: CharParsing p => IdentifierStyle p
enameStyle = IdentifierStyle "name" (lower <|> char '_') nameChar reserved Identifier ReservedIdentifier

onameStyle :: CharParsing p => IdentifierStyle p
onameStyle = IdentifierStyle "operator" opChar opChar mempty Highlight.Operator ReservedOperator

tnameStyle :: CharParsing p => IdentifierStyle p
tnameStyle = IdentifierStyle "type name" upper nameChar reserved Identifier ReservedIdentifier


arrow :: TokenParsing p => p String
arrow = symbol "->"

lparen :: TokenParsing p => p Char
lparen = symbolic '('

rparen :: TokenParsing p => p Char
rparen = symbolic ')'

lbrace :: TokenParsing p => p Char
lbrace = symbolic '{'

rbrace :: TokenParsing p => p Char
rbrace = symbolic '}'


anned :: (Has Parser sig p, Has (Writer (Snoc (Span, S.Comment))) sig p) => p a -> p (S.Ann a)
anned p = mk <$> censor @(Snoc (Span, S.Comment)) (const Nil) (listen @(Snoc (Span, S.Comment)) ((,,) <$> position <*> p <*> position))
  where
  mk (cs, (s, a, e)) = S.Ann (Span s e) cs a


-- Parsing carriers

runFacet :: Functor m => [Operator (S.Ann S.Expr)] -> Facet m a -> m a
runFacet ops (Facet m) = snd <$> C.runWriter (runWriterC (C.evalState ops (runStateC m)))

newtype Facet m a = Facet (StateC [Operator (S.Ann S.Expr)] (WriterC (Snoc (Span, S.Comment)) m) a)
  deriving (Algebra (State [Operator (S.Ann S.Expr)] :+: Writer (Snoc (Span, S.Comment)) :+: sig), Alternative, Applicative, Functor, Monad, MonadFail, MonadFix)

instance (Monad p, Parsing p) => Parsing (Facet p) where
  try (Facet m) = Facet $ try m
  Facet m <?> l = Facet $ m <?> l
  unexpected = lift . unexpected
  eof = lift eof
  notFollowedBy (Facet m) = Facet $ notFollowedBy m

instance (Monad p, CharParsing p) => CharParsing (Facet p) where
  satisfy = lift . satisfy
  char    = lift . char
  notChar = lift . notChar
  anyChar = lift anyChar
  string  = lift . string
  text    = lift . text

instance (Has Parser sig p, TokenParsing p) => TokenParsing (Facet p) where
  someSpace = skipSome (void (satisfy isSpace) <|> lineComment)
    where
    lineComment = (do
      start <- position
      void $ char '#'
      comment <- many (satisfy (/= '\n'))
      end <- position
      tell (Nil :> (Span start end, S.Comment (pack comment)))) <?> "line comment"

instance MonadTrans Facet where
  lift = Facet . lift . lift


newtype StateC s m a = StateC { runStateC :: C.StateC s m a }
  deriving (Algebra (State s :+: sig), Alternative, Applicative, Functor, Monad, MonadFail, MonadFix, MonadTrans)

instance (Monad p, Parsing p) => Parsing (StateC s p) where
  try (StateC m) = StateC $ C.StateC $ \ s -> try (C.runState s m)
  StateC m <?> l = StateC $ C.StateC $ \ s -> C.runState s m <?> l
  unexpected = lift . unexpected
  eof = lift eof
  notFollowedBy (StateC m) = StateC $ C.StateC $ \ s -> (s,) <$> notFollowedBy (C.evalState s m)


newtype WriterC w m a = WriterC { runWriterC :: C.WriterC w m a }
  deriving (Algebra (Writer w :+: sig), Alternative, Applicative, Functor, Monad, MonadFail, MonadFix, MonadTrans)

instance (Monad p, Parsing p) => Parsing (WriterC s p) where
  try (WriterC (C.WriterC m)) = WriterC $ C.WriterC $ C.StateC $ \ s -> try (C.runState s m)
  WriterC (C.WriterC m) <?> l = WriterC $ C.WriterC $ C.StateC $ \ s -> C.runState s m <?> l
  unexpected = lift . unexpected
  eof = lift eof
  notFollowedBy (WriterC (C.WriterC m)) = WriterC $ C.WriterC $ C.StateC $ \ s -> (s,) <$> notFollowedBy (C.evalState s m)


newtype ReaderC r m a = ReaderC { runReaderC :: C.ReaderC r m a }
  deriving (Algebra (Reader r :+: sig), Alternative, Applicative, Functor, Monad, MonadFail, MonadFix, MonadTrans)

instance (Monad p, Parsing p) => Parsing (ReaderC r p) where
  try (ReaderC m) = ReaderC $ C.ReaderC $ try . (`C.runReader` m)
  ReaderC m <?> l = ReaderC $ C.ReaderC $ \ r -> C.runReader r m <?> l
  unexpected = lift . unexpected
  eof = lift eof
  notFollowedBy (ReaderC m) = ReaderC $ C.ReaderC $ \ r -> notFollowedBy (C.runReader r m)

instance (Monad p, CharParsing p) => CharParsing (ReaderC r p) where
  satisfy = lift . satisfy
  {-# INLINE satisfy #-}
  char    = lift . char
  {-# INLINE char #-}
  notChar = lift . notChar
  {-# INLINE notChar #-}
  anyChar = lift anyChar
  {-# INLINE anyChar #-}
  string  = lift . string
  {-# INLINE string #-}
  text = lift . text
  {-# INLINE text #-}

instance (Monad p, TokenParsing p) => TokenParsing (ReaderC r p) where
  nesting (ReaderC m) = ReaderC $ C.ReaderC $ nesting . (`C.runReader` m)
  {-# INLINE nesting #-}
  someSpace = lift someSpace
  {-# INLINE someSpace #-}
  semi      = lift semi
  {-# INLINE semi #-}
  highlight h (ReaderC m) = ReaderC $ C.ReaderC $ highlight h . (`C.runReader` m)
  {-# INLINE highlight #-}
