{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
module Facet.Parser
( Pos(..)
, Span(..)
, Symbol(..)
, Parsing(..)
, (<?>)
, string
, set
, opt
, many
, some
, span
, spanned
, Parser(..)
, State(..)
, Source(..)
, sourceFromString
, takeLine
, substring
, (!)
, Excerpt(..)
, excerpted
, Level(..)
, prettyLevel
, Notice(..)
, prettyNotice
, Token(..)
, parseString
, parse
, tokenize
, parser
, parens
, braces
) where

import           Data.Bifunctor (first)
import qualified Data.CharSet as CharSet
import qualified Data.CharSet.Unicode as CharSet
import           Data.List (isSuffixOf)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Prelude hiding (fail, lines, null, span)
import           Prettyprinter hiding (braces, line, parens)
import           Prettyprinter.Render.Terminal as ANSI

data Pos = Pos { line :: {-# unpack #-} !Int, col :: {-# unpack #-} !Int }
  deriving (Eq, Ord, Show)

data Span = Span { start :: {-# unpack #-} !Pos, end :: {-# unpack #-} !Pos }
  deriving (Eq, Ord, Show)

instance Semigroup Span where
  Span s1 e1 <> Span s2 e2 = Span (min s1 s2) (max e1 e2)

class (Monoid (Set sym), Ord sym, Show sym) => Symbol sym where
  type Set sym
  singleton :: sym -> Set sym
  member :: sym -> Set sym -> Bool
  toList :: Set sym -> [sym]

instance Symbol Char where
  type Set Char = CharSet.CharSet
  singleton = CharSet.singleton
  member    = CharSet.member
  toList    = CharSet.toList

class Applicative p => Parsing p where
  position :: p Pos
  source :: p Source
  symbol :: Char -> p Char
  (<|>) :: p a -> p a -> p a
  infixl 3 <|>
  fail :: a -> String -> p a

-- FIXME: always require <?>/fail to terminate a chain of alternatives
(<?>) :: Parsing p => p a -> (a, String) -> p a
p <?> (a, s) = p <|> fail a s
infixl 2 <?>

string :: Parsing p => String -> p String
string s = foldr ((*>) . symbol) (pure s) s <?> (s, s)

set :: Parsing p => CharSet.CharSet -> (Maybe Char -> t) -> String -> p t
set t f s = foldr ((<|>) . fmap (f . Just) . symbol) (fail (f Nothing) s) (toList t)

opt :: Parsing p => p a -> a -> p a
opt p v = p <|> pure v

many :: Parsing p => p a -> p [a]
many p = go where go = opt ((:) <$> p <*> go) []

some :: Parsing p => p a -> p [a]
some p = (:) <$> p <*> many p

span :: Parsing p => p a -> p Span
span p = Span <$> position <* p <*> position

spanned :: Parsing p => p a -> p (Span, a)
spanned p = mk <$> position <*> p <*> position
  where
  mk s a e = (Span s e, a)


combine :: Semigroup t => Bool -> t -> t -> t
combine e s1 s2
  | e         = s1 <> s2
  | otherwise = s1


data Null a
  = Null   (State -> a)
  | Insert (State -> a) (State -> [Notice])
  deriving (Functor)

nullable :: Null a -> Bool
nullable p = case p of
  Null  _    -> True
  Insert _ _ -> False

getNull :: Null a -> State -> a
getNull (Null   f)   = f
getNull (Insert f _) = f

getErrors :: Null a -> State -> [Notice]
getErrors (Null   _)   = const []
getErrors (Insert _ f) = f

instance Applicative Null where
  pure = Null . pure
  f <*> a = case f of
    Null   f    -> case a of
      Null   a    -> Null   (f <*> a)
      Insert a sa -> Insert (f <*> a) sa
    Insert f sf -> Insert (f <*> getNull a) (combine (not (nullable a)) sf (getErrors a))

inserted :: String -> State -> Notice
inserted s i = Notice (Just Error) (stateExcerpt i) (pretty "inserted" <+> pretty s) []

deleted :: String -> State -> Notice
deleted  s i = Notice (Just Error) (stateExcerpt i) (pretty "deleted"  <+> pretty s) []

alt :: Null a -> Null a -> Null a
alt l@Null{} _ = l
alt _        r = r

choose :: Null a -> Map.Map Char (ParserCont a) -> ParserCont a
choose p choices = go
  where
  go i noskip = case input i of
    []  -> insertOrNull p i
    s:_ -> let s' = tokenSymbol s in case Map.lookup s' choices of
      Nothing
        | any (member s') noskip -> insertOrNull p i
        | otherwise              -> choose p choices (advance i{ errs = errs i ++ [ deleted (show s') i ] }) noskip
      Just k -> k i noskip

insertOrNull :: Null a -> State -> (State, a)
insertOrNull n i = case n of
  Null   a   -> (i, a i)
  Insert a e -> (i{ errs = errs i ++ e i }, a i)

data Parser a = Parser
  { null     :: Null a
  , firstSet :: CharSet.CharSet
  , table    :: [(Char, ParserCont a)]
  }
  deriving (Functor)

type ParserCont a = State -> [CharSet.CharSet] -> (State, a)

data State = State
  { src   :: Source
  , input :: [Token]
  , errs  :: [Notice]
  , pos   :: {-# unpack #-} !Pos
  }

advance :: State -> State
advance (State s i es _) = State s (tail i) es (end (tokenSpan (head i)))

stateExcerpt :: State -> Excerpt
stateExcerpt i = Excerpt (path (src i)) (src i ! pos i) (Span (pos i) (pos i))


data Source = Source
  { path  :: Maybe FilePath
  , lines :: [String]
  }
  deriving (Eq, Ord, Show)

sourceFromString :: Maybe FilePath -> String -> Source
sourceFromString path = Source path . go
  where
  go = \case
    "" -> [""]
    s  -> let (line, rest) = takeLine s in line : either (const []) go rest
{-# inline sourceFromString #-}

takeLine :: String -> (String, Either String String)
takeLine = go id where
  go line = \case
    ""        -> (line "", Left "")
    '\r':rest -> case rest of
      '\n':rest -> (line "\r\n", Right rest)
      _         -> (line "\r", Right rest)
    '\n':rest -> (line "\n", Right rest)
    c   :rest -> go (line . (c:)) rest
{-# inline takeLine #-}

substring :: Source -> Span -> String
substring source (Span (Pos sl sc) (Pos el ec)) = concat (onHead (drop sc) (onLast (take ec) (drop sl (take el (lines source)))))
  where
  onHead f = \case
    []   -> []
    x:xs -> f x : xs
  onLast f = go
    where
    go = \case
      []   -> []
      [x]  -> [f x]
      x:xs -> x:go xs

(!) :: Source -> Pos -> String
Source _ lines ! pos = lines !! line pos
{-# INLINE (!) #-}

infixl 9 !


data Excerpt = Excerpt
  { excerptPath :: !(Maybe FilePath)
  , excerptLine :: !String
  , excerptSpan :: {-# UNPACK #-} !Span
  }
  deriving (Eq, Ord, Show)

excerpted :: Parsing p => p a -> p (Excerpt, a)
excerpted p = first . mk <$> source <*> spanned p
  where
  mk src span = Excerpt (path src) (src ! start span) span


data Level
  = Warn
  | Error
  deriving (Eq, Ord, Show)

prettyLevel :: Level -> Doc AnsiStyle
prettyLevel = \case
  Warn  -> magenta (pretty "warning")
  Error -> red     (pretty "error")


data Notice = Notice
  { level   :: !(Maybe Level)
  , excerpt :: {-# UNPACK #-} !Excerpt
  , reason  :: !(Doc AnsiStyle)
  , context :: ![Doc AnsiStyle]
  }
  deriving (Show)

prettyNotice :: Notice -> Doc AnsiStyle
prettyNotice (Notice level (Excerpt path text span) reason context) = vsep
  ( nest 2 (group (fillSep
    [ bold (pretty (fromMaybe "(interactive)" path)) <> colon <> pos (start span) <> colon <> foldMap ((space <>) . (<> colon) . prettyLevel) level
    , reason
    ]))
  : blue (pretty (succ (line (start span)))) <+> align (vcat
    [ blue (pretty '|') <+> if "\n" `isSuffixOf` text then pretty (init text) <> blue (pretty "\\n") else pretty text <> blue (pretty "<end of input>")
    , blue (pretty '|') <+> padding span <> caret span
    ])
  : context)
  where
  pos (Pos l c) = bold (pretty (succ l)) <> colon <> bold (pretty (succ c))

  padding (Span (Pos _ c) _) = pretty (replicate c ' ')

  caret (Span start@(Pos sl sc) end@(Pos el ec))
    | start == end = green (pretty '^')
    | sl    == el  = green (pretty (replicate (ec - sc) '~'))
    | otherwise    = green (pretty "^…")

  bold = annotate ANSI.bold


red, green, blue, magenta :: Doc AnsiStyle -> Doc AnsiStyle
red     = annotate $ color Red
green   = annotate $ color Green
blue    = annotate $ color Blue
magenta = annotate $ color Magenta


data Token = Token
  { tokenSymbol :: Char
  , tokenSource :: Maybe String -- ^ will be Nothing for tokens for which it would be constant
  , tokenSpan   :: Span
  }
  deriving (Show)

instance Applicative Parser where
  pure a = Parser (pure a) mempty []
  Parser nf ff tf <*> ~(Parser na fa ta) = Parser (nf <*> na) (combine (nullable nf) ff fa) $ tseq tf ta
    where
    choices = Map.fromList ta
    tseq tf ta = combine (nullable nf) tabf taba
      where
      tabf = map (fmap (\ k i noskip ->
        let (i', f')  = k i (fa:noskip)
            (i'', a') = choose na choices i' noskip
            fa'       = f' a'
        in  fa' `seq` (i'', fa'))) tf
      taba = map (fmap (\ k i noskip ->
        let (i', a') = k i noskip
            fa'      = getNull nf i' a'
        in  fa' `seq` (i', fa'))) ta

instance Parsing Parser where
  position = Parser (Null pos) mempty []
  source = Parser (Null src) mempty []
  symbol s = Parser (Insert (const s) (pure <$> inserted (show s))) (singleton s) [ (s, \ i _ -> (advance i, s)) ]
  -- FIXME: warn on non-disjoint first sets
  pl <|> pr = Parser (null pl `alt` null pr) (firstSet pl <> firstSet pr) (table pl <> table pr)
  fail a e = Parser (Insert (const a) (pure <$> inserted e)) mempty []

parseString :: Maybe FilePath -> Parser a -> String -> ([Notice], a)
parseString path p s = first errs (parse p (sourceFromString path s) (tokenize s))

parse :: Parser a -> Source -> [Token] -> (State, a)
parse p ls s = choose (null p) choices (State ls s mempty (Pos 0 0)) mempty
  where
  choices = Map.fromList (table p)

tokenize :: String -> [Token]
tokenize = go (Pos 0 0)
  where
  go _ []     = []
  go p@(Pos l c) (x:xs) = Token x Nothing (Span p p') : go p' xs
    where
    p' = case x of
      '\n' -> Pos (l + 1) 0
      _    -> Pos l       (c + 1)


parser :: Parsing p => p [Name]
parser = ws *> many (some (ident <* ws))
  where
  ident = set (CharSet.fromList ['a'..'z']) (fromMaybe '_') "letter"
  ws = let c = set (CharSet.separator <> CharSet.control) (const ()) "whitespace" in opt (c <* ws) ()


parens :: Parsing p => p a -> p a
parens a = symbol '(' *> a <* symbol ')'

braces :: Parsing p => p a -> p a
braces a = symbol '{' *> a <* symbol '}'


type Name = String
