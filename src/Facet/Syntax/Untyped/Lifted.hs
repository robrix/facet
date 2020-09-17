{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Syntax.Untyped.Lifted
( S.Expr
, lam
, lam0
, ($$)
) where

import           Control.Applicative (liftA2)
import           Facet.Functor.C
import qualified Facet.Syntax.Untyped as S

lam
  :: (Applicative m, Permutable env, S.Expr repr)
  => (forall env' . Permutable env' => (env :.: env') (Either repr (repr, repr -> repr)) -> (m :.: (env :.: env')) repr)
  -> (m :.: env) repr
lam f = S.lam <$> C (getC <$> getC (f (C (pure id))))

lam0
  :: (Applicative m, Permutable env, S.Expr repr)
  => (forall env' . Permutable env' => (env :.: env') repr -> (m :.: (env :.: env')) repr)
  -> (m :.: env) repr
lam0 f = S.lam0 <$> C (getC <$> getC (f (C (pure id))))

($$) :: (Applicative m, Applicative env, S.Expr expr) => m (env expr) -> m (env expr) -> m (env expr)
f $$ a = liftA2 (liftA2 (S.$$)) f a

infixl 9 $$
