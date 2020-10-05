{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Surface.Decl
( Decl(..)
, (>=>)
, unForAll
, (>->)
, (.=)
, DeclF(..)
, fold
) where

import Control.Category ((>>>))
import Control.Effect.Empty
import Facet.Name
import Facet.Surface.Expr (Expr)
import Facet.Surface.Type (Type)
import Facet.Syntax ((:::)(..))
import Text.Parser.Position (Span, Spanned(..))

newtype Decl = In { out :: DeclF Decl }

instance Spanned Decl where
  setSpan = fmap In . Loc

  dropSpan = out >>> \case
    Loc _ d -> dropSpan d
    d       -> In d

-- | Universal quantification.
(>=>) :: (Name ::: Type) -> Decl -> Decl
(>=>) = fmap In . (:=>)

infixr 1 >=>

unForAll :: Has Empty sig m => Decl -> m (Name ::: Type, Decl)
unForAll d = case out d of
  t :=> b -> pure (t, b)
  _       -> empty

(>->) :: (Name ::: Type) -> Decl -> Decl
(>->) = fmap In . (:->)

infixr 1 >->

(.=) :: Type -> Expr -> Decl
(.=) = fmap In . (:=)

infix 1 .=


data DeclF a
  = (Name ::: Type) :=> a
  | (Name ::: Type) :-> a
  | Type := Expr
  | Loc Span a
  deriving (Foldable, Functor, Traversable)

infix 1 :=
infixr 1 :=>
infixr 1 :->


fold :: (DeclF a -> a) -> Decl -> a
fold alg = go
  where
  go = alg . fmap go . out
