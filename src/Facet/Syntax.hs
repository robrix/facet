{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Syntax
( (:::)(..)
, tm
, ty
, (:=:)(..)
  -- * Variables
, Var(..)
  -- * Decomposition
, splitl
, splitr
  -- * Universes
, T
, N
, P
, Some(..)
, mapSome
, foldSome
) where

import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Functor.Classes
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


-- Variables

data Var m a
  = Global (Q Name) -- ^ Global variables, considered equal by 'Q' 'Name'.
  | Free a
  | Metavar m
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


-- Universes

-- | Type tag for the type universe (“types”).
type T = P -- FIXME: this is bad, but convenient

-- | Type tag for the negative type universe (“computations”).
data N

-- | Type tag for the positive type universe (“values”).
data P

data Some t where
  SomeT :: t T -> Some t
  SomeN :: t N -> Some t
  SomeP :: t P -> Some t

instance (forall x . Eq (t x)) => Eq (Some t) where
  SomeT t1 == SomeT t2 = t1 == t2
  SomeT{}  == _        = False
  SomeN t1 == SomeN t2 = t1 == t2
  SomeN{}  == _        = False
  SomeP t1 == SomeP t2 = t1 == t2
  SomeP{}  == _        = False

instance (forall x . Show (t x)) => Show (Some t) where
  showsPrec p = foldSome (showsUnaryWith showsPrec "Some" p)

mapSome :: (forall u . t u -> t' u) -> Some t -> Some t'
mapSome f = \case
  SomeT t -> SomeT (f t)
  SomeN t -> SomeN (f t)
  SomeP t -> SomeP (f t)

foldSome :: (forall u . t u -> a) -> Some t -> a
foldSome f = \case
  SomeT t -> f t
  SomeN t -> f t
  SomeP t -> f t
