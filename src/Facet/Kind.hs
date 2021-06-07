module Facet.Kind
( Kind(..)
) where

import Facet.Name

-- Kinds

data Kind
  = KType
  | KInterface
  | KArrow (Maybe Name) Kind Kind
  deriving (Eq, Ord, Show)
