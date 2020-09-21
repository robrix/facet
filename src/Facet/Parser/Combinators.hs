{-# LANGUAGE TypeOperators #-}
module Facet.Parser.Combinators
( Parsing(..)
, char
, oneOfSet
, (<?>)
, string
, opt
, skipMany
, skipSome
, chainr
, chainl
, chainr1
, chainl1
, sepBy
, sepBy1
, span
, spanned
, parens
, braces
, brackets
, token
, ws
  -- * Character parsers
, lower
, upper
, letter
, colon
, comma
, lparen
, rparen
, lbrace
, rbrace
, lbracket
, rbracket
  -- * Re-exports
, Alternative(..)
, optional
) where

import           Control.Applicative (Alternative(..), liftA2, optional, (<**>))
import qualified Data.Char as Char
import qualified Data.CharSet as CharSet
import qualified Data.CharSet.Unicode as CharSet
import           Data.Foldable (traverse_)
import           Facet.Functor.C
import           Facet.Parser.Source
import           Facet.Parser.Span
import           Prelude hiding (span)

class Alternative p => Parsing p where
  position :: p Pos

  satisfy :: (Char -> Bool) -> p Char

  source :: p Source

  -- FIXME: allow failure values to produce errors from the state
  errorWith :: a -> String -> p a

  -- | Parse some text, and then parse something else constructed using a parser that parses the same literal text.
  --
  -- This is like a restricted form of the monadic bind.
  --
  -- FIXME: this is a bad name.
  capture :: (a -> b -> c) -> p a -> (p a -> p b) -> p c

  -- | Like capture, but the higher-order parser receives a pure parser instead of a parser of the same text.
  --
  -- FIXME: this is a bad name.
  capture0 :: (a -> b -> c) -> p a -> (p a -> p b) -> p c

  {-# MINIMAL position, satisfy, source, errorWith, capture, capture0 #-}

instance (Parsing f, Applicative g) => Parsing (f :.: g) where
  position = C $ pure <$> position
  satisfy p = C $ pure <$> satisfy p
  source   = C $ pure <$> source
  errorWith a s = C $ errorWith (pure a) s
  capture f p g = C $ capture (liftA2 f) (getC p) (getC . g . C)
  capture0 f p g = C $ capture0 (liftA2 f) (getC p) (getC . g . C)

char :: Parsing p => Char -> p Char
char c = satisfy (== c) <|> errorWith c (show c)

oneOfSet :: Parsing p => CharSet.CharSet -> p Char
oneOfSet t = satisfy (`CharSet.member` t)

-- FIXME: always require <?>/errorWith to terminate a chain of alternatives
(<?>) :: Parsing p => p a -> (a, String) -> p a
p <?> (a, s) = p <|> errorWith a s
infixl 2 <?>

string :: Parsing p => String -> p String
string s = s <$ traverse_ char s <?> (s, s)

opt :: Parsing p => p a -> a -> p a
opt p v = p <|> pure v

skipMany :: Parsing p => p a -> p ()
skipMany p = go where go = opt (p *> go) ()

skipSome :: Parsing p => p a -> p ()
skipSome p = p *> skipMany p

chainr :: Parsing p => p a -> p (a -> a -> a) -> a -> p a
chainr p = opt . chainr1 p

chainl :: Parsing p => p a -> p (a -> a -> a) -> a -> p a
chainl p = opt . chainl1 p

chainl1 :: Parsing p => p a -> p (a -> a -> a) -> p a
chainl1 p op = p <**> go
  where
  go = opt ((\ f y g x -> g (f x y)) <$> op <*> p <*> go) id

chainr1 :: Parsing p => p a -> p (a -> a -> a) -> p a
chainr1 p op = go
  where
  go = p <**> opt (flip <$> op <*> go) id

sepBy :: Parsing p => p a -> p s -> p [a]
sepBy p s = opt (sepBy1 p s) []

sepBy1 :: Parsing p => p a -> p s -> p [a]
sepBy1 p s = (:) <$> p <*> many (s *> p)

span :: Parsing p => p a -> p Span
span p = Span <$> position <* p <*> position

spanned :: Parsing p => p a -> p (Span, a)
spanned p = mk <$> position <*> p <*> position
  where
  mk s a e = (Span s e, a)


parens :: Parsing p => p a -> p a
parens a = lparen *> a <* rparen

braces :: Parsing p => p a -> p a
braces a = lbrace *> a <* rbrace

brackets :: Parsing p => p a -> p a
brackets a = lbracket *> a <* rbracket


token :: Parsing p => p a -> p a
token p = p <* ws


-- Character parsers

lower, upper, letter :: Parsing p => p Char
lower = oneOfSet CharSet.lowercaseLetter <|> errorWith 'a' "lowercase letter"
upper = oneOfSet CharSet.uppercaseLetter <|> errorWith 'A' "uppercase letter"
letter = oneOfSet CharSet.letter <|> errorWith 'a' "letter"

colon, comma :: Parsing p => p Char
colon = token (char ':')
comma = token (char ',')

lparen, rparen :: Parsing p => p Char
lparen = token (char '(')
rparen = token (char ')')

lbrace, rbrace :: Parsing p => p Char
lbrace = token (char '{')
rbrace = token (char '}')

lbracket, rbracket :: Parsing p => p Char
lbracket = token (char '[')
rbracket = token (char ']')

ws :: Parsing p => p ()
ws = skipMany space

space :: Parsing p => p Char
space = satisfy Char.isSpace <|> errorWith ' ' "space"
