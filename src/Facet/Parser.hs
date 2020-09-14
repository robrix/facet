{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
module Facet.Parser
( Pos(..)
, Span(..)
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
, parseString
, parse
, parser
, parens
, braces
) where

import           Data.Bifunctor (first)
import           Data.CharSet (CharSet, fromList, member, singleton, toList)
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

position :: Parser Pos
position = Parser (Null pos) mempty []

char :: Char -> Parser Char
char s = Parser (Insert (const s) (pure <$> inserted (show s))) (singleton s) [ (s, \ i _ -> (advance i, s)) ]

source :: Parser Source
source = Parser (Null src) mempty []

-- FIXME: warn on non-disjoint first sets
(<|>) :: Parser a -> Parser a -> Parser a
pl <|> pr = Parser (null pl `alt` null pr) (firstSet pl <> firstSet pr) (table pl <> table pr)
infixl 3 <|>

fail :: a -> String -> Parser a
fail a e = Parser (Insert (const a) (pure <$> inserted e)) mempty []

-- FIXME: always require <?>/fail to terminate a chain of alternatives
(<?>) :: Parser a -> (a, String) -> Parser a
p <?> (a, s) = p <|> fail a s
infixl 2 <?>

string :: String -> Parser String
string s = foldr ((*>) . char) (pure s) s <?> (s, s)

set :: CharSet -> (Maybe Char -> t) -> String -> Parser t
set t f s = foldr ((<|>) . fmap (f . Just) . char) (fail (f Nothing) s) (toList t)

opt :: Parser a -> a -> Parser a
opt p v = p <|> pure v

many :: Parser a -> Parser [a]
many p = go where go = opt ((:) <$> p <*> go) []

some :: Parser a -> Parser [a]
some p = (:) <$> p <*> many p

span :: Parser a -> Parser Span
span p = Span <$> position <* p <*> position

spanned :: Parser a -> Parser (Span, a)
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
    s:_ -> case Map.lookup s choices of
      Nothing
        | any (member s) noskip -> insertOrNull p i
        | otherwise             -> choose p choices (advance i{ errs = errs i ++ [ deleted (show s) i ] }) noskip
      Just k -> k i noskip

insertOrNull :: Null a -> State -> (State, a)
insertOrNull n i = case n of
  Null   a   -> (i, a i)
  Insert a e -> (i{ errs = errs i ++ e i }, a i)

data Parser a = Parser
  { null     :: Null a
  , firstSet :: CharSet
  , table    :: [(Char, ParserCont a)]
  }
  deriving (Functor)

type ParserCont a = State -> [CharSet] -> (State, a)

data State = State
  { src   :: Source
  , input :: String
  , errs  :: [Notice]
  , pos   :: {-# unpack #-} !Pos
  }

advance :: State -> State
advance (State s i es (Pos l c)) = State s (tail i) es p
  where
  p = case head i of
    '\n' -> Pos (l + 1) 0
    _    -> Pos l       (c + 1)


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

excerpted :: Parser a -> Parser (Excerpt, a)
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

parseString :: Maybe FilePath -> Parser a -> String -> ([Notice], a)
parseString path p s = first errs (parse p (sourceFromString path s) s)

parse :: Parser a -> Source -> String -> (State, a)
parse p ls s = choose (null p) choices (State ls s mempty (Pos 0 0)) mempty
  where
  choices = Map.fromList (table p)


parser :: Parser [Name]
parser = ws *> many (ident <* ws)

lower' = fromList ['a'..'z']
lower = set lower' (fromMaybe 'a') "lowercase letter"
upper' = fromList ['A'..'Z']
upper = set upper' (fromMaybe 'A') "uppercase letter"
letter = lower <|> upper <?> ('a', "letter")
ident = (:) <$> lower <*> many letter
ws = let c = set (CharSet.separator <> CharSet.control) (const ()) "whitespace" in opt (c <* ws) ()


parens :: Parser a -> Parser a
parens a = char '(' *> a <* char ')'

braces :: Parser a -> Parser a
braces a = char '{' *> a <* char '}'


type Name = String
