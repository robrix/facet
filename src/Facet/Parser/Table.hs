{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
module Facet.Parser.Table
( Assoc(..)
, Operator(..)
, parseOperator
, OperatorParser
, Table
, build
, terminate
) where

import Control.Applicative (Alternative(..))
import Data.Foldable (foldl')
import Data.Function ((&))
import Data.Text (Text)
import Text.Parser.Combinators
import Text.Parser.Position
import Text.Parser.Token

data Assoc = N | L | R

data Operator p a
  -- TODO: prefix, postfix, mixfix
  = Prefix  Text (a -> a)
  | Postfix Text (a -> a)
  | Infix Assoc Text (a -> a -> a)
  | Outfix Text Text (a -> a)
  | Operator (OperatorParser p a)
  | Atom (p a)

parseOperator :: (PositionParsing p, Spanned a) => Operator p a -> OperatorParser p a
parseOperator = \case
  Prefix   s op -> \ self _    -> op <$ textSymbol s <*> self
  Postfix  s op -> \ _    next -> foldl' (&) <$> next <*> many (op <$ textSymbol s)
  Infix N  s op -> \ _    next -> try (op <$> next <* textSymbol s) <*> next
  Infix L  s op -> \ _    next -> chainl1Loc next (op <$ textSymbol s)
  Infix R  s op -> \ self next -> try (op <$> next <* textSymbol s) <*> self
  Outfix s e op -> \ self _    -> op <$ textSymbol s <*> nesting self <* textSymbol e
  Operator p    -> p
  Atom p        -> const (const p)

type OperatorParser p a = p a -> p a -> p a
type Table p a = [[Operator p a]]

-- | Build a parser for a Table.
build :: (PositionParsing p, Spanned a) => Table p a -> (p a -> p a) -> p a
build ts end = root
  where
  root = foldr chain (end root) ts
  chain ps next = self
    where
    self = foldr (\ p rest -> parseOperator p self next <|> rest) next ps

terminate :: (p a -> p a) -> OperatorParser p a -> p a -> p a
terminate wrap op next = self where self = wrap $ op self next
