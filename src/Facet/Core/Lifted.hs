{-# LANGUAGE RankNTypes #-}
module Facet.Core.Lifted
( -- * Types
  C.Type
, _Type
, _Unit
, (.*)
, (.$)
, (-->)
, (>=>)
  -- * Expressions
, C.Expr(($$))
, lam0
  -- * Re-exports
, Extends
, (>>>)
, castF
, refl
, strengthen
) where

import           Control.Applicative (liftA2)
import qualified Facet.Core as C
import           Facet.Env

-- Types

_Type :: (Applicative m, Applicative env, C.Type ty) => m (env ty)
_Type = pure (pure C._Type)

_Unit :: (Applicative m, Applicative env, C.Type ty) => m (env ty)
_Unit = pure (pure C._Unit)

(.*) :: (Applicative m, Applicative env, C.Type ty) => m (env ty) -> m (env ty) -> m (env ty)
(.*) = liftA2 (liftA2 (C..*))

infixl 7 .*

(.$) :: (Applicative m, Applicative env, C.Type ty) => m (env ty) -> m (env ty) -> m (env ty)
(.$) = liftA2 (liftA2 (C..$))

infixl 9 .$

(-->) :: (Applicative m, Applicative env, C.Type ty) => m (env ty) -> m (env ty) -> m (env ty)
(-->) = liftA2 (liftA2 (C.-->))

infixr 2 -->

-- | Universal quantification.
(>=>)
  :: (Applicative m, Applicative env, C.Type ty)
  => m (env ty)
  -> (forall env' . Applicative env' => Extends env env' -> env' ty -> m (env' ty))
  -> m (env ty)
t >=> b = liftA2 (C.>=>) <$> t <*> liftBinder b

infixr 1 >=>


-- Expressions

lam0
  :: (Applicative m, Applicative env, C.Expr expr)
  => (forall env' . Applicative env' => Extends env env' -> env' expr -> m (env' expr))
  -> m (env expr)
lam0 f = fmap C.lam0 <$> liftBinder f
