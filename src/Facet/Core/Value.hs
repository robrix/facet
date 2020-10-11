{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core.Value
( Value(..)
, Type
, Expr
, global
, bound
, unForAll
, unTLam
, unArrow
, unLam
, unProductT
, ($$)
, ($$*)
, foldContext
, foldContextAll
, close
, closeAll
) where

import Control.Effect.Empty
import Control.Monad ((<=<))
import Data.Foldable (foldl')
import Facet.Name
import Facet.Stack
import Facet.Syntax

-- FIXME: should the domain of the binders be f a instead of Value f a?
-- FIXME: should bound variables be f a instead of a?
data Value f a
  = Type
  | Void
  | UnitT
  | Unit
  | (UName ::: Value f a) :=> (Value f a -> f (Value f a))
  | TLam UName (Value f a -> f (Value f a))
  | Value f a :-> Value f a
  | Lam UName (Value f a -> f (Value f a))
  | Either QName a :$ Stack (Value f a)
  | TPrd (Value f a) (Value f a)
  | Prd (Value f a) (Value f a)

infixr 0 :=>
infixl 9 :$
infixr 0 :->


type Type = Value
type Expr = Value


global :: QName -> Value f a
global n = Left n :$ Nil

bound :: a -> Value f a
bound n = Right n :$ Nil


unForAll :: Has Empty sig m => Value f a -> m (UName ::: Value f a, Value f a -> f (Value f a))
unForAll = \case{ t :=> b -> pure (t, b) ; _ -> empty }

unTLam :: Has Empty sig m => Value f a -> m (UName, Value f a -> f (Value f a))
unTLam = \case{ TLam n b -> pure (n, b) ; _ -> empty }

unArrow :: Has Empty sig m => Value f a -> m (Value f a, Value f a)
unArrow = \case{ a :-> b -> pure (a, b) ; _ -> empty }

unLam :: Has Empty sig m => Value f a -> m (UName, Value f a -> f (Value f a))
unLam = \case{ Lam n b -> pure (n, b) ; _ -> empty }

unProductT :: Has Empty sig m => Value f a -> m (Value f a, Value f a)
unProductT = \case{ TPrd l r -> pure (l, r) ; _ -> empty }


($$) :: Applicative f => Value f a -> Value f a -> f (Value f a)
(f :$ as) $$ a = pure (f :$ (as :> a))
(_ :=> b) $$ a = b a
TLam _ b  $$ a = b a
Lam  _ b  $$ a = b a
_         $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: (Foldable t, Monad f) => Value f a -> t (Value f a) -> f (Value f a)
f $$* as = foldl' (\ f a -> f >>= ($$ a)) (pure f) as

infixl 9 $$, $$*


foldContext :: Monad m => (Stack a -> Value m a -> m a) -> Stack a -> Value m Level -> m a
foldContext fold env = fold env <=< go env
  where
  go env = \case
    Type     -> pure Type
    Void     -> pure Void
    UnitT    -> pure UnitT
    Unit     -> pure Unit
    t :=> b  -> do
      t' <- traverse (go env) t
      pure $ t' :=> \ v -> do
        b' <- b (bound (Level (length env)))
        v' <- fold env v
        go (env:>v') b'
    a :-> b  -> (:->) <$> go env a <*> go env b
    TLam n b -> pure $ TLam n $ \ v -> do
      b' <- b (bound (Level (length env)))
      v' <- fold env v
      go (env:>v') b'
    Lam  n b -> pure $ Lam  n $ \ v -> do
      b' <- b (bound (Level (length env)))
      v' <- fold env v
      go (env:>v') b'
    f :$ as  -> do
      let f' = either global (bound . (env !) . getIndex . levelToIndex (Level (length env))) f
      as' <- traverse (go env) as
      f' $$* as'
    TPrd l r -> TPrd <$> go env l <*> go env r
    Prd  l r -> Prd  <$> go env l <*> go env r

foldContextAll :: Monad m => (Stack a -> Value m a -> m a) -> Stack (Value m Level) -> m (Stack a)
foldContextAll fold = go
  where
  go Nil     = pure Nil
  go (as:>a) = do
    as' <- go as
    a'  <- foldContext fold as' a
    pure $ as' :> a'


-- FIXME: these are pretty clearly broken; we should define them in terms of an interpreter.
close :: Monad m => Stack (Value m a) -> Value m Level -> m (Value m a)
close env = \case
  Type     -> pure Type
  Void     -> pure Void
  UnitT    -> pure UnitT
  Unit     -> pure Unit
  t :=> b  -> do
    t' <- traverse (close env) t
    pure $ t' :=> \ v -> close (env:>v) =<< b (bound (Level (length env)))
  a :-> b  -> (:->) <$> close env a <*> close env b
  TLam n b -> pure $ TLam n $ \ v -> close (env:>v) =<< b (bound (Level (length env)))
  Lam  n b -> pure $ Lam  n $ \ v -> close (env:>v) =<< b (bound (Level (length env)))
  f :$ as  -> do
    let f' = either global ((env !) . getIndex . levelToIndex (Level (length env))) f
    as' <- traverse (close env) as
    f' $$* as'
  TPrd l r -> TPrd <$> close env l <*> close env r
  Prd l r  -> Prd  <$> close env l <*> close env r

closeAll :: Monad m => Stack (Value m Level) -> m (Stack (Value m a))
closeAll = \case
  Nil     -> pure Nil
  as :> a -> do
    as' <- closeAll as
    a'  <- close as' a
    pure $ as' :> a'
