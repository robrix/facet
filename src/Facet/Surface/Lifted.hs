{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Surface.Lifted
( S.Name
, S.TName
, S.Expr(global, unit, (**), ($$))
, S.Type(tglobal, _Type, _Unit, (-->), (.*), (.$))
, S.Module(..)
, S.Decl((.=))
, S.ForAll
, (S.:::)(..)
, lam
, lam0
, (>=>)
, (>->)
  -- * Re-exports
, Extends
, (>>>)
, castF
, refl
, strengthen
) where

import           Control.Applicative (liftA2)
import           Facet.Env (Extends, castF, liftBinder, refl, strengthen, (>>>))
import qualified Facet.Surface as S

lam
  :: (Applicative m, Applicative env, S.Expr repr)
  => (forall env' . Applicative env' => Extends env env' -> env' (Either repr (repr, repr -> repr)) -> m (env' repr))
  -> m (env repr)
lam f = fmap S.lam <$> liftBinder f

lam0
  :: (Applicative m, Applicative env, S.Expr repr)
  => (forall env' . Applicative env' => Extends env env' -> env' repr -> m (env' repr))
  -> m (env repr)
lam0 f = fmap S.lam0 <$> liftBinder f


(>=>)
  :: (Applicative m, Applicative env, S.ForAll ty decl)
  => m (env (S.TName S.::: ty))
  -> (forall env' . Applicative env' => Extends env env' -> env' ty -> m (env' decl))
  -> m (env decl)
t >=> b = liftA2 (S.>=>) <$> t <*> liftBinder b

infixr 1 >=>

(>->)
  :: (Applicative m, Applicative env, S.Decl expr ty decl)
  => m (env ty)
  -> (forall env' . Applicative env' => Extends env env' -> env' expr -> m (env' decl))
  -> m (env decl)
t >-> b = liftA2 (S.>->) <$> t <*> liftBinder b

infixr 1 >->
