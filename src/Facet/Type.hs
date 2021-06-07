{-# LANGUAGE PolyKinds #-}
module Facet.Type
( TType(..)
, Comp
) where

import Data.Kind (Type)
import Data.Text (Text)
import Data.Void (Void)
import Facet.Interface (Interface, Signature)
import Facet.Kind (Kind)
import Facet.Name (Name)
import Facet.Syntax (T)
import Facet.Usage (Quantity)

data Comp a

class TType (ty :: forall k . k -> Type) where
  string :: ty Text
  forAll :: Name -> T Kind a -> (ty a -> ty b) -> ty (a -> b)
  arrow :: Maybe Name -> Quantity -> ty a -> ty b -> ty (a -> b)
  comp :: Signature (ty (Interface Void)) -> ty a -> ty (Comp a)
  app :: ty (f :: j -> k) -> ty (a :: j) -> ty k
