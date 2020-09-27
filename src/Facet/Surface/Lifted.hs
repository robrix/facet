{-# LANGUAGE RankNTypes #-}
module Facet.Surface.Lifted
( S.Name
, S.Expr(global, unit, (**), ($$))
, S.Type(tglobal, _Type, _Unit, (-->), (.*), (.$))
, S.Module(..)
, S.Decl((.=))
, S.ForAll
, lam
, lam0
, (>=>)
, (>->)
  -- * Re-exports
, Extends
, Permutable
, (>>>)
, castF
, refl
, strengthen
) where

import           Control.Applicative (liftA2)
import           Facet.Env (Extends, Permutable, castF, liftBinder, refl, strengthen, (>>>))
import qualified Facet.Surface as S

lam
  :: (Applicative m, Permutable env, S.Expr repr)
  => (forall env' . Permutable env' => Extends env env' -> env' (Either repr (repr, repr -> repr)) -> m (env' repr))
  -> m (env repr)
lam f = fmap S.lam <$> liftBinder f

lam0
  :: (Applicative m, Permutable env, S.Expr repr)
  => (forall env' . Permutable env' => Extends env env' -> env' repr -> m (env' repr))
  -> m (env repr)
lam0 f = fmap S.lam0 <$> liftBinder f


(>=>)
  :: (Applicative m, Permutable env, S.ForAll ty decl)
  => m (env ty)
  -> (forall env' . Permutable env' => Extends env env' -> env' ty -> m (env' decl))
  -> m (env decl)
t >=> b = liftA2 (S.>=>) <$> t <*> liftBinder b

infixr 1 >=>

(>->)
  :: (Applicative m, Permutable env, S.Decl expr ty decl)
  => m (env ty)
  -> (forall env' . Permutable env' => Extends env env' -> env' expr -> m (env' decl))
  -> m (env decl)
t >-> b = liftA2 (S.>->) <$> t <*> liftBinder b

infixr 1 >->
