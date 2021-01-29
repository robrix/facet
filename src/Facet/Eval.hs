{-# LANGUAGE GADTs #-}
module Facet.Eval
( -- * Evaluation
  Value(..)
, eval
  -- * Machinery
, runEval
, Eval(..)
) where

import Control.Monad.Trans.Class
import Facet.Core.Term
import Facet.Name
import Facet.Syntax

newtype Value = Value { getValue :: Expr }
  deriving (Eq, Ord, Show)

eval :: Expr -> Eval m Value
eval = \case
  -- XApp op a -> _
  -- VNe (h :$ sp) -> do
  --   sp' <- traverse (traverse eval) sp
  --   mod <- lift ask
  --   graph <- lift ask
  --   case h of
  --     Global q
  --       | Just (_ :=: Just (DTerm v) ::: _) <- lookupQ q mod graph
  --       -> eval $ v $$* sp'
  --     _ -> pure $ VNe (h :$ sp')

  -- VTComp (Sig _ []) v -> eval v

  -- XOp op    -> Eval $ \ h -> h op

  v         -> pure (Value v)


-- Machinery

runEval :: (Q Name :$ Value -> (Value -> m r) -> m r) -> (a -> m r) -> Eval m a -> m r
runEval hdl k (Eval m) = m hdl k

newtype Eval m a = Eval (forall r . (Q Name :$ Value -> (Value -> m r) -> m r) -> (a -> m r) -> m r)

instance Functor (Eval m) where
  fmap f (Eval m) = Eval $ \ hdl k -> m hdl (k . f)

instance Applicative (Eval m) where
  pure a = Eval $ \ _ k -> k a
  f <*> a = Eval $ \ hdl k -> runEval hdl (\ f' -> runEval hdl (\ a' -> k $! f' a') a) f

instance Monad (Eval m) where
  m >>= f = Eval $ \ hdl k -> runEval hdl (runEval hdl k . f) m

instance MonadTrans Eval where
  lift m = Eval $ \ _ k -> m >>= k
