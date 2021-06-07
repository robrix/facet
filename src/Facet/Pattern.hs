module Facet.Pattern
( -- * Patterns
  Pattern(..)
, fill
) where

import Data.Traversable (mapAccumL)
import Facet.Name
import Facet.Syntax

-- Patterns

data Pattern a
  = PWildcard
  | PVar a
  | PCon RName [Pattern a]
  | PDict [RName :=: a]
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)


fill :: Traversable t => (b -> (b, c)) -> b -> t a -> (b, t c)
fill f = mapAccumL (const . f)
