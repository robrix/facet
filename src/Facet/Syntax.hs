{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
module Facet.Syntax
( -- * Expressions
  Expr(..)
, Inst(..)
, absurdI
, val
, lam0
, (<&)
, (&>)
  -- * Types
, Type(..)
  -- * Modules
, DeclName
, Module(..)
, Decl(..)
  -- * Effects
, State(..)
, Empty(..)
  -- * Examples
, id'
, const'
, flip'
, curry'
, uncurry'
, get
, put
, runState
, execState
, postIncr
, empty
, runEmpty
, execEmpty
  -- * Signatures
, module Facet.Signature
) where

import Data.Functor.Sum
import Facet.Signature

-- Expressions

class (forall sig . Applicative (repr sig)) => Expr repr where
  -- FIXME: patterns
  lam :: (Either (repr None a) (Inst eff (repr (Sum eff sig) a)) -> repr sig b) -> repr sig (repr (Sum eff sig) a -> repr sig b)
  ($$) :: repr sig (repr sig' a -> repr sig b) -> repr sig' a -> repr sig b
  infixl 9 $$

  alg :: sig k -> (k -> repr sig a) -> repr sig a

  weakenBy :: (forall x . sub x -> sup x) -> repr sub a -> repr sup a

  -- FIXME: constructors
  -- FIXME: patterns

data Inst eff a
  = forall k . Inst (eff k) (k -> a)

deriving instance Functor (Inst eff)

absurdI :: Inst None a -> b
absurdI (Inst e _) = absurd e


-- | Values embed into computations at every signature.
val :: Expr repr => repr None a -> repr sig a
val = weakenBy absurd

lam0 :: Expr repr => (repr None a -> repr sig b) -> repr sig (repr sig a -> repr sig b)
lam0 f = (. weakenBy InR) <$> lam (f . either id absurdI)


(<&) :: Expr repr => repr sig a -> repr sig b -> repr sig a
a <& b = const' $$ a $$ b

(&>) :: Expr repr => repr sig a -> repr sig b -> repr sig b
a &> b = flip' $$ const' $$ a $$ b

infixl 1 <&, &>


-- Types

class Type ty where
  (-->) :: ty expr a -> ty expr b -> ty expr (expr a -> expr b)
  infixr 2 -->

  (.*) :: ty expr a -> ty expr b -> ty expr (a, b)
  infixl 7 .*

  _Unit :: ty expr ()


-- Modules

type DeclName = String

class (Decl expr ty decl, Applicative mod) => Module expr ty decl mod | mod -> decl ty expr where
  (.:) :: DeclName -> decl a -> mod (decl a)
  infixr 0 .:

class (Expr expr, Type ty) => Decl expr ty decl | decl -> ty expr where
  forAll :: (ty (expr sig) a -> decl b) -> decl b
  (>->) :: ty (expr sig) a -> (expr sig a -> decl b) -> decl (expr sig a -> b)
  infixr 1 >->
  (.=) :: ty (expr sig) a -> expr sig a -> decl a
  infix 1 .=



-- Effects

data State s k where
  Get :: State s s
  Put :: s -> State s ()

data Empty k = Empty


-- Examples

id' :: Expr repr => repr sig (repr sig a -> repr sig a)
id' = lam0 val

const' :: Expr repr => repr sig (repr sig a -> repr sig (repr sig b -> repr sig a))
const' = lam0 (lam0 . const . val)

flip' :: Expr repr => repr sig (repr sig (repr sig a -> repr sig (repr sig b -> repr sig c)) -> repr sig (repr sig b -> repr sig (repr sig a -> repr sig c)))
flip' = lam0 (\ f -> lam0 (\ b -> lam0 (\ a -> val f $$ val a $$ val b)))

curry' :: Expr repr => repr sig (repr sig (repr sig (a, b) -> repr sig c) -> repr sig (repr sig a -> repr sig (repr sig b -> repr sig c)))
curry' = lam0 $ \ f -> lam0 $ \ a -> lam0 $ \ b -> val f $$ ((,) <$> val a <*> val b)

uncurry' :: Expr repr => repr sig (repr sig (repr sig a -> repr sig (repr sig b -> repr sig c)) -> repr sig (repr sig (a, b) -> repr sig c))
uncurry' = lam0 $ \ f -> lam0 $ \ ab -> val f $$ fmap fst (val ab) $$ fmap snd (val ab)

get :: (Expr repr, Member (State (repr None s)) sig) => repr sig s
get = alg (inj Get) val

put :: (Expr repr, Member (State (repr None s)) sig) => repr sig (repr sig s -> repr sig ())
put = lam0 $ \ s -> alg (inj (Put s)) pure

runState :: Expr repr => repr sig (repr sig s -> repr sig (repr (Sum (State (repr None s)) sig) a -> repr sig (s, a)))
runState = lam0 $ \ s -> lam $ \case
  Left a                -> (,) <$> val s <*> val a
  Right (Inst Get     k) -> runState $$ val s $$ k s
  Right (Inst (Put s) k) -> runState $$ val s $$ k ()

execState :: Expr repr => repr sig (repr sig s -> repr sig (repr (Sum (State (repr None s)) sig) a -> repr sig a))
execState = lam0 $ \ s -> lam $ \case
  Left a                -> val a
  Right (Inst Get     k) -> execState $$ val s $$ k s
  Right (Inst (Put s) k) -> execState $$ val s $$ k ()


postIncr :: forall repr sig . (Expr repr, Num (repr sig Int), Member (State (repr None Int)) sig) => repr sig Int
postIncr = get <& put $$ (get + 1 :: repr sig Int)


empty :: (Expr repr, Member Empty sig) => repr sig a
empty = alg (inj Empty) pure

runEmpty :: Expr repr => repr sig (repr sig a -> repr sig (repr (Sum Empty sig) a -> repr sig a))
runEmpty = lam0 $ \ a -> lam $ \case
  Left x               -> val x
  Right (Inst Empty _) -> val a

execEmpty :: Expr repr => repr sig (repr (Sum Empty sig) a -> repr sig Bool)
execEmpty = lam (either (const (pure True)) (const (pure False)))
