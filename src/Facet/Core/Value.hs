{-# LANGUAGE TypeOperators #-}
module Facet.Core.Value
( Value(..)
, global
, bound
) where

import Facet.Core.Pattern
import Facet.Name
import Facet.Stack
import Facet.Syntax

data Value f a
  = Type
  | Void
  | Unit
  | (UName ::: Value f a) :=> (Value f a -> f (Value f a))
  | Either QName a :$ Stack (Value f a)
  | Value f a :-> Value f a
  | Value f a :*  Value f a
  | TLam UName (Value f a -> f (Value f a))
  | Lam (Pattern UName) (Pattern (Value f a) -> f (Value f a))

infixr 0 :=>
infixl 9 :$
infixr 0 :->
infixl 7 :*


global :: QName -> Value f a
global n = Left n :$ Nil

bound :: a -> Value f a
bound n = Right n :$ Nil
