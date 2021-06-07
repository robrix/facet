{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Eval
( -- * Evaluation
  eval
  -- * Machinery
, Eval(..)
  -- * Values
, Value(..)
, unit
  -- * Quotation
, quoteV
, E(..)
, runE
, state'
, state''
, State'(..)
, Reader'(..)
-- , Empty(..)
, toMaybe
, send'
, modify
, get''
, put''
, ask''
, local''
, reader'
) where

import Control.Algebra
import Control.Carrier.Reader
import Control.Monad (ap, guard, liftM, (>=>))
import Control.Monad.Trans.Class
import Data.Foldable
import Data.Function
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Facet.Env as Env
import Facet.Graph
import Facet.Module
import Facet.Name hiding (Op)
import Facet.Pattern
import Facet.Semialign (zipWithM)
import Facet.Snoc.NonEmpty as NE hiding ((|>))
import Facet.Syntax
import Facet.Term
import GHC.Stack (HasCallStack)
import Prelude hiding (zipWith)

eval :: (HasCallStack, Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Expr -> ReaderC (Env (Value (Eval m))) (Eval m) (Value (Eval m))
eval = \case
  XVar (Global n) -> global n >>= eval
  XVar (Free n)   -> var n
  XLam cs         -> lam cs
  XApp  f a       -> app (eval f) a
  XCon n fs       -> con n (eval <$> fs)
  XString s       -> string s
  XDict os        -> VDict <$> traverse (traverse eval) os
  XLet p v b      -> eval v >>= \ v' -> local (|> fromMaybe (error "eval: non-exhaustive pattern in let") (matchV id p v')) (eval b)
  XComp p b       -> comp p b

global :: Has (Reader Graph :+: Reader Module) sig m => RName -> ReaderC (Env (Value (Eval m))) (Eval m) Expr
global n = do
  mod <- lift ask
  graph <- lift ask
  case lookupQ graph mod (toQ n) of
    [_ :=: DTerm (Just v) _] -> pure v -- FIXME: store values in the module graph
    _                        -> error "throw a real error here"

var :: (HasCallStack, Algebra sig m) => LName Index -> ReaderC (Env (Value m)) m (Value m)
var n = asks (`index` n)

lam :: Algebra sig m => [(Pattern Name, Expr)] -> ReaderC (Env (Value (Eval m))) (Eval m) (Value (Eval m))
lam cs = asks (`VLam` cs)

app :: (HasCallStack, Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => ReaderC (Env (Value (Eval m))) (Eval m) (Value (Eval m)) -> Expr -> ReaderC (Env (Value (Eval m))) (Eval m) (Value (Eval m))
app f a = ask >>= \ envCallSite -> f >>= \case
  VLam env cs -> lift (k a) where
    k = foldl' (\ vs (p, b) -> runReader envCallSite . eval >=> fromMaybe (vs a) . matchV (\ vs -> runReader (env |> vs) (eval b)) p) (const (fail "non-exhaustive patterns in lambda")) cs
  VCont k     -> lift (k =<< runReader envCallSite (eval a))
  _           -> fail "expected lambda/continuation"

string :: Text -> ReaderC (Env (Value (Eval m))) (Eval m) (Value (Eval m))
string = pure . VString

con :: RName -> [ReaderC (Env (Value (Eval m))) (Eval m) (Value (Eval m))] -> ReaderC (Env (Value (Eval m))) (Eval m) (Value (Eval m))
con n fs = VCon n <$> sequenceA fs

comp :: [RName :=: Name] -> Expr -> ReaderC (Env (Value (Eval m))) (Eval m) (Value (Eval m))
comp p b = pure $ VComp p b


-- Machinery

newtype Eval m a = Eval { runEval :: forall r . (a -> m r) -> m r }

instance Functor (Eval m) where
  fmap = liftM

instance Applicative (Eval m) where
  pure a = Eval $ \ k -> k a
  (<*>) = ap

instance Monad (Eval m) where
  m >>= f = Eval $ \ k -> runEval m (\ a -> runEval (f a) k)

instance MonadFail m => MonadFail (Eval m) where
  fail = lift . fail

instance MonadTrans Eval where
  lift m = Eval $ \ k -> m >>= k

instance Algebra sig m => Algebra sig (Eval m) where
  alg hdl sig ctx = Eval $ \ k -> alg (\ m -> runEval (hdl m) pure) sig ctx >>= k


-- Values

data Value m
  -- | Neutral; variables, only used during quotation
  = VVar (Var (LName Level))
  -- | Value; data constructors.
  | VCon RName [Value m]
  -- | Value; strings.
  | VString Text
  -- | Computation; lambdas.
  | VLam (Env (Value m)) [(Pattern Name, Expr)]
  -- | Computation; continuations, used in effect handlers.
  | VCont (Value m -> m (Value m))
  | VDict [RName :=: Value m]
  | VComp [RName :=: Name] Expr

unit :: Value m
unit = VCon (NE.FromList ["Data", "Unit"] :.: U "unit") []


-- Elimination

matchV :: (Pattern (Name :=: Value m) -> a) -> Pattern Name -> Value m -> Maybe a
matchV k p s = case p of
  PWildcard -> pure (k PWildcard)
  PVar n    -> pure (k (PVar (n :=: s)))
  PCon n ps
    | VCon n' fs <- s -> k . PCon n' <$ guard (n == n') <*> zipWithM (matchV id) ps fs
  PCon{}    -> Nothing
  PDict ps
    | VDict os <- s -> k . PDict <$> zipWithM (\ (n1 :=: p) (n2 :=: o) -> (n1 :=: (p :=: o)) <$ guard (n1 == n2)) ps os
  PDict{}   -> Nothing


-- Quotation

quoteV :: Monad m => Level -> Value m -> m Expr
quoteV d = \case
  VLam _ cs -> pure $ XLam cs
  VCont k   -> quoteV (succ d) =<< k (VVar (Free (LName d __)))
  VVar v    -> pure (XVar (fmap (levelToIndex d) <$> v))
  VCon n fs -> XCon n <$> traverse (quoteV d) fs
  VString s -> pure $ XString s
  VDict os  -> XDict <$> traverse (traverse (quoteV d)) os
  VComp p b -> pure $ XComp p b


newtype E sig r a = E (forall i . sig (E sig) i r -> (a -> r) -> r)
  deriving (Functor)

instance Applicative (E sig r) where
  pure a = E $ \ _ k -> k a
  (<*>) = ap

instance Monad (E sig r) where
  E run >>= f = E $ \ d k -> run d (runE d k . f)

runE :: sig (E sig) i r -> (a -> r) -> E sig r a -> r
runE d k (E run) = run d k


newtype Empty m a b = Empty { empty :: forall e . (e -> m b a) -> b }

toMaybe :: E Empty (Maybe a) a -> Maybe a
toMaybe = runE Empty{ empty = const Nothing } Just


data Reader' r m a b = Reader'
  { ask'   :: (r -> m b a) -> b
  , local' :: forall x . (r -> r) -> m x x -> (x -> m b a) -> b }

ask'' :: E (Reader' r) b r
ask'' = send' ask'

local'' :: (r -> r) -> E (Reader' r) a a -> E (Reader' r) a a
local'' f m = send' (\ Reader'{ local' } -> local' f m)

reader' :: r -> E (Reader' r) a a -> a
reader' r = runE dict id
  where
  dict = Reader'
    { ask'   = \     k -> reader' r (k r)
    , local' = \ f m k -> reader' r (k (reader' (f r) m))
    }


data State' s m a b = State'
  { get' :: (s -> m b a) -> b
  , put' :: s -> (() -> m b a) -> b }

send' :: (forall i . sig (E sig) i b -> (c -> E sig b i) -> b) -> E sig b c
send' hdl = E $ \ d k -> hdl d (\ c -> E (\ _ _ -> k c))

state'' :: s -> E (State' s) (s -> (s, a)) a -> (s, a)
state'' = state' (,)

state' :: (s -> a -> b) -> s -> E (State' s) (s -> b) a -> b
state' z s m = runE dict (flip z) m s
  where
  dict = State'
    { get' = \   k s -> state' z s (k s)
    , put' = \ s k _ -> state' z s (k ()) }

modify :: (s -> s) -> E (State' s) r ()
modify f = put'' . f =<< get''

get'' :: E (State' s) r s
get'' = send' get'

put'' :: s -> E (State' s) r ()
put'' s = send' (`put'` s)
