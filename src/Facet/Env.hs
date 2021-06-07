module Facet.Env
( Env(..)
, empty
, (|>)
, lookup
, index
, level
) where

import Control.Applicative ((<|>))
import Control.Monad (guard)
import Data.Maybe (fromMaybe)
import Facet.Name
import Facet.Pattern
import Facet.Snoc
import Facet.Syntax
import GHC.Stack
import Prelude hiding (lookup)

newtype Env v = Env { bindings :: Snoc (Pattern (Name :=: v)) }
  deriving (Foldable, Functor, Monoid, Semigroup, Traversable)

empty :: Env v
empty = Env Nil

(|>) :: Env v -> Pattern (Name :=: v) -> Env v
Env vs |> v = Env (vs :> v)

infixl 5 |>

lookup :: Env v -> LName Index -> Maybe v
lookup (Env vs) (LName i n) = find (\ (n' :=: v) -> v <$ guard (n == n')) (vs ! getIndex i)
  where
  find f = foldr ((<|>) . f) Nothing

index :: HasCallStack => Env v -> LName Index -> v
index env n = fromMaybe (error ("Env.index: name (" <> show n <> ") not found")) (lookup env n)

level :: Env v -> Level
level = Level . length . bindings
