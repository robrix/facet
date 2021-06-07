module Facet.Type.Expr
( Type(..)
) where

import Facet.Interface
import Facet.Kind
import Facet.Name
import Facet.Syntax
import Facet.Type
import Facet.Usage

data Type
  = String
  | Var (Var (Either Meta (LName Index)))
  | ForAll Name Kind Type
  | Arrow (Maybe Name) Quantity Type Type
  | Comp (Signature Type) Type
  | App Type Type
  deriving (Eq, Ord, Show)

-- FIXME: this should be Level -> Type
instance TType (T (Level -> Type)) where
  string = T (const String)
  forAll n (T k) b = T (\ d -> ForAll n k (getT (b (T (\ d' -> Var (Free (Right (LName (levelToIndex d d') n)))))) d))
  arrow n q (T a) (T b) = T (\ d -> Arrow n q (a d) (b d))
  comp sig (T b) = T (\ d -> Comp (mapSignature (\ (T i) -> i d) sig) (b d))
  app (T f) (T a) = T (\ d -> App (f d) (a d))
