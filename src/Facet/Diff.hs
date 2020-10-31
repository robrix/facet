module Facet.Diff
( applyChange
) where

import           Control.Monad (guard, (<=<))
import qualified Data.IntMap as IntMap
import           Data.Void
import           Facet.Name (Meta(..))
import           Facet.Surface

applyChange :: (Expr Meta, Expr Meta) -> (Expr Void) -> Maybe (Expr Void)
applyChange (d, i) = ins i <=< del d

del :: Expr Meta -> Expr Void -> Maybe (IntMap.IntMap (Expr Void))
del = go IntMap.empty
  where
  go m = curry $ \case
    (Var m1 n1, Var m2 n2)   -> m <$ guard (m1 == m2 && n1 == n2)
    (Var{}, _)               -> Nothing
    (Hole n1, Hole n2)       -> m <$ guard (n1 == n2)
    (Hole{}, _)              -> Nothing
    (Type, Type)             -> pure m
    (Type, _)                -> Nothing
    (TInterface, TInterface) -> pure m
    (TInterface, _)          -> Nothing
    (TString, TString)       -> pure m
    (TString, _)             -> Nothing
    (Thunk e1, Thunk e2)     -> goAnn (go m) e1 e2
    (Thunk{}, _)             -> Nothing
    (Force e1, Force e2)     -> goAnn (go m) e1 e2
    (Force{}, _)             -> Nothing
    (App f1 a1, App f2 a2)   -> goAnn (go m) f1 f2 >>= \ m' -> goAnn (go m') a1 a2
    (App{}, _)               -> Nothing
    (As e1 t1, As e2 t2)     -> goAnn (go m) e1 e2 >>= \ m' -> goAnn (go m') t1 t2
    (As{}, _)                -> Nothing
    (String s1, String s2)   -> m <$ guard (s1 == s2)
    (M i, t)                 -> case IntMap.lookup (getMeta i) m of { Nothing -> pure (IntMap.insert (getMeta i) t m) ; Just t' -> m <$ guard (t == t') }
    -- FIXME: TComp, Lam
    _                        -> Nothing

  goAnn :: (t -> u -> Maybe x) -> Ann t -> Ann u -> Maybe x
  goAnn go (Ann _ c1 e1) (Ann _ c2 e2) = guard (c1 == c2) *> go e1 e2


ins :: Expr Meta -> IntMap.IntMap (Expr Void) -> Maybe (Expr Void)
ins d m = case d of
  M i -> IntMap.lookup (getMeta i) m
  s   -> traverse (const Nothing) s
