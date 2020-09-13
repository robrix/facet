{-# LANGUAGE FunctionalDependencies #-}
module Facet.Parser
( Parsing(..)
, Parser(..)
, Nullable(..)
) where

import Control.Applicative

class Alternative p => Parsing s p | p -> s where
  symbol :: s -> p s
  (<?>) :: p a -> (a, String) -> p a

newtype Parser s a = Parser { runParser :: () }

newtype Nullable a = Nullable { getNullable :: Bool }
