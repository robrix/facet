module Facet.Context
( -- * Contexts
  Quantity
, Context(..)
, empty
, (|>)
, level
, (!)
, lookupIndex
, toEnv
) where

import qualified Control.Effect.Empty as E
import           Data.Foldable (find, toList)
import qualified Facet.Env as Env
import           Facet.Name
import           Facet.Pattern
import qualified Facet.Snoc as S
import           Facet.Syntax
import           Facet.Type.Norm
import           Facet.Usage
import           GHC.Stack
import           Prelude hiding (lookup)

newtype Context = Context { elems :: S.Snoc (Quantity, Pattern (Name ::: Classifier)) }


empty :: Context
empty = Context S.Nil

(|>) :: Context -> (Quantity, Pattern (Name ::: Classifier)) -> Context
Context as |> a = Context (as S.:> a)

infixl 5 |>

level :: Context -> Level
level (Context es) = Level (length es)

(!) :: HasCallStack => Context -> Index -> (Quantity, Pattern (Name ::: Classifier))
Context es' ! Index i' = withFrozenCallStack $ go es' i'
  where
  go (es S.:> e) i
    | i == 0       = e
    | otherwise    = go es (i - 1)
  go _           _ = error $ "Facet.Context.!: index (" <> show i' <> ") out of bounds (" <> show (length es') <> ")"

lookupIndex :: E.Has E.Empty sig m => Name -> Context -> m (LName Index, Quantity, Classifier)
lookupIndex n = go (Index 0) . elems
  where
  go _ S.Nil                                        = E.empty
  go i (cs S.:> (q, p))
    | Just (n' ::: t) <- find ((== n) . tm) p = pure (LName i n', q, t)
    | otherwise                                     = go (succ i) cs


toEnv :: Context -> Env.Env Type
toEnv c = Env.Env (S.fromList (zipWith (\ (_, p) d -> (\ b -> tm b :=: free (LName d (tm b))) <$> p) (toList (elems c)) [0..pred (level c)]))
