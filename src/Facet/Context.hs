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
, toEnv
) where

import qualified Control.Effect.Empty as E
import           Data.Foldable (find, toList)
import           Facet.Core.Pattern
import           Facet.Core.Type
import qualified Facet.Env as Env
import           Facet.Name
import qualified Facet.Snoc as S
import           Facet.Syntax
import           Facet.Usage
import           GHC.Stack
import           Prelude hiding (lookup)

newtype Context = Context { elems :: S.Snoc (Quantity, Pattern Binding) }

data Binding = Binding
  { name  :: Name
  , type' :: Classifier
  }


empty :: Context
empty = Context S.Nil

(|>) :: Context -> (Quantity, Pattern Binding) -> Context
Context as |> a = Context (as S.:> a)

infixl 5 |>

level :: Context -> Level
level (Context es) = Level (length es)

(!) :: HasCallStack => Context -> Index -> (Quantity, Pattern Binding)
Context es' ! Index i' = withFrozenCallStack $ go es' i'
  where
  go (es S.:> e) i
    | i == 0       = e
    | otherwise    = go es (i - 1)
  go _           _ = error $ "Facet.Context.!: index (" <> show i' <> ") out of bounds (" <> show (length es') <> ")"

lookupIndex :: E.Has E.Empty sig m => Name -> Context -> m (Index, Name, Quantity, Classifier)
lookupIndex n = go (Index 0) . elems
  where
  go _ S.Nil                                        = E.empty
  go i (cs S.:> (q, p))
    | Just (Binding n' t) <- find ((== n) . name) p = pure (i, n', q, t)
    | otherwise                                     = go (succ i) cs


toEnv :: Context -> Env.Env Type
toEnv c = Env.Env (S.fromList (zipWith (\ (_, p) d -> (\ b -> name b :=: free d (name b)) <$> p) (toList (elems c)) [0..pred (level c)]))
