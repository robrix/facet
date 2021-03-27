module Facet.Context
( -- * Contexts
  Quantity
, Context(..)
, Binding(..)
, empty
, (|>)
, level
, (!)
, lookupIndex
) where

import qualified Control.Effect.Empty as E
import           Facet.Core.Type
import           Facet.Name
import qualified Facet.Snoc as S
import           Facet.Usage
import           GHC.Stack
import           Prelude hiding (lookup, zipWith)

newtype Context = Context { elems :: S.Snoc Binding }

data Binding = Binding
  { name     :: Name
  , quantity :: Quantity
  , type'    :: Classifier
  }


empty :: Context
empty = Context S.Nil

(|>) :: Context -> Binding -> Context
Context as |> a = Context (as S.:> a)

infixl 5 |>

level :: Context -> Level
level (Context es) = Level (length es)

(!) :: HasCallStack => Context -> Index -> Binding
Context es' ! Index i' = withFrozenCallStack $ go es' i'
  where
  go (es S.:> e) i
    | i == 0       = e
    | otherwise    = go es (i - 1)
  go _           _ = error $ "Facet.Context.!: index (" <> show i' <> ") out of bounds (" <> show (length es') <> ")"

lookupIndex :: E.Has E.Empty sig m => Name -> Context -> m (Index, Quantity, Classifier)
lookupIndex n = go (Index 0) . elems
  where
  go _ S.Nil            = E.empty
  go i (cs S.:> Binding n' q t)
    | n == n'           = pure (i, q, t)
    | otherwise         = go (succ i) cs
