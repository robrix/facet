{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core.Lifted
( -- * Types
  C.Type
, _Type
, _Unit
, (>=>)
, (.$)
, (-->)
, (.*)
, C.Interpret(..)
  -- * Expressions
, C.Expr(($$))
, lam0
  -- * Re-exports
, Extends(..)
, (>>>)
, castF
, refl
, strengthen
, weaken
) where

import           Control.Applicative (liftA2)
import           Control.Monad.Fix
import           Data.Text (Text)
import qualified Facet.Core as C
import           Facet.Env
import           Facet.Name
import           Facet.Syntax

-- Types

_Type :: (C.Type ty, Applicative m) => m ty
_Type = pure C._Type

_Unit :: (C.Type ty, Applicative m) => m ty
_Unit = pure C._Unit


(>=>)
  :: (C.Type ty, Scoped ty, MonadFix m)
  => m (Text ::: ty)
  -> (ty -> m ty)
  -> m ty
t >=> b = t >>= \ (n ::: t) -> binderM C.tbound ((C.>=>) . (::: t)) n b

infixr 1 >=>

(.$) :: (C.Type ty, Applicative m) => m ty -> m ty -> m ty
(.$) = liftA2 (C..$)

infixl 9 .$


(-->) :: (C.Type ty, Applicative m) => m ty -> m ty -> m ty
(-->) = liftA2 (C.-->)

infixr 2 -->

(.*) :: (C.Type ty, Applicative m) => m ty -> m ty -> m ty
(.*) = liftA2 (C..*)

infixl 7 .*


-- Expressions

lam0
  :: (C.Expr expr, Scoped expr, MonadFix m)
  => Text
  -> (expr -> m expr)
  -> m expr
lam0 = binderM C.bound C.lam0
