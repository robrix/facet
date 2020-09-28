{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Syntax
( (:::)(..)
, tm
, ty
, uncurryAnn
, (.:)
) where

import Data.Bifunctor
import Facet.Name

data a ::: b = a ::: b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infix 5 :::

instance Bifunctor (:::) where
  bimap f g (a ::: b) = f a ::: g b

instance (Scoped a, Scoped b) => Scoped (a ::: b) where
  maxBV (a ::: b) = maxBV a `max` maxBV b

tm :: a ::: b -> a
tm (a ::: _) = a

ty :: a ::: b -> b
ty (_ ::: b) = b


uncurryAnn :: (a -> b -> c) -> ((a ::: b) -> c)
uncurryAnn f ~(a ::: b) = f a b


(.:) :: Functor m => m a -> b -> m (a ::: b)
tm .: ty = (::: ty) <$> tm

infix 5 .:
