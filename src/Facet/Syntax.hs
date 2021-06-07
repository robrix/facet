{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
module Facet.Syntax
( (:::)(..)
, tm
, ty
, (:=:)(..)
, nm, def
  -- * Variables
, Var(..)
  -- * Decomposition
, splitl
, splitr
  -- * Assertion data
, Exp(..)
, Act(..)
  -- * Type-safe constructors
, T(..)
) where

import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Functor.Classes
import Data.Kind (Type)
import Facet.Name
import Facet.Snoc

data a ::: b = a ::: b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 2 :::

instance Bifoldable (:::) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (:::) where
  bimap = bimapDefault

instance Bitraversable (:::) where
  bitraverse f g (a ::: b) = (:::) <$> f a <*> g b

instance Eq a => Eq1 ((:::) a) where
  liftEq = liftEq2 (==)

instance Ord a => Ord1 ((:::) a) where
  liftCompare = liftCompare2 compare

instance Eq2 (:::) where
  liftEq2 eqA eqB (a1 ::: b1) (a2 ::: b2) = eqA a1 a2 && eqB b1 b2

instance Ord2 (:::) where
  liftCompare2 compareA compareB (a1 ::: b1) (a2 ::: b2) = compareA a1 a2 <> compareB b1 b2

tm :: a ::: b -> a
tm (a ::: _) = a

ty :: a ::: b -> b
ty (_ ::: b) = b


data a :=: b = a :=: b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 2 :=:

instance Bifoldable (:=:) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (:=:) where
  bimap = bimapDefault

instance Bitraversable (:=:) where
  bitraverse f g (a :=: b) = (:=:) <$> f a <*> g b

nm :: a :=: b -> a
nm (a :=: _) = a

def :: a :=: b -> b
def (_ :=: b) = b


-- Variables

data Var a
  = Global RName -- ^ Global variables, considered equal by 'RName'.
  | Free a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)


-- Decomposition

splitl :: (t -> Maybe (t, a)) -> t -> (t, Snoc a)
splitl un = go id
  where
  go as t = case un t of
    Just (t', a) -> go (as . (:> a)) t'
    Nothing      -> (t, as Nil)

splitr :: (t -> Maybe (a, t)) -> t -> ([a], t)
splitr un = go id
  where
  go as t = case un t of
    Just (a, t') -> go (as . (a:)) t'
    Nothing      -> (as [], t)


-- Assertion data

newtype Exp a = Exp { getExp :: a }
  deriving (Functor)

newtype Act a = Act { getAct :: a }
  deriving (Functor)


-- Type-safe constructors

type T :: Type -> forall k . k -> Type

newtype T a b = T { getT :: a }
