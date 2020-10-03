{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Facet.Surface.Expr
( EName(..)
, Expr(..)
, global
, bound
, lam
, ($$)
, unit
, (**)
, ExprF(..)
, fold
) where

import Control.Effect.Parser.Span (Span)
import Data.String (IsString(..))
import Data.Text (Text)
import Facet.Name
import Prelude hiding ((**))
import Prettyprinter (Pretty)

newtype EName = EName { getEName :: Text }
  deriving (Eq, IsString, Ord, Pretty, Show)

newtype Expr = In { out :: ExprF Expr }

global :: EName -> Expr
global = In . Free

bound :: Name -> Expr
bound = In . Bound

lam :: Name -> Expr -> Expr
lam = fmap In . Lam

($$) :: Expr -> Expr -> Expr
($$) = fmap In . (:$)

infixl 9 $$

unit :: Expr
unit = In Unit

-- | Tupling.
(**) :: Expr -> Expr -> Expr
(**) = fmap In . (:*)

-- FIXME: tupling/unit should take a list of expressions


data ExprF e
  = Free EName
  | Bound Name
  | Lam Name e
  | e :$ e
  | Unit
  | e :* e
  | Ann Span e
  deriving (Foldable, Functor, Traversable)

infixl 9 :$
infixl 7 :*


fold :: (ExprF a -> a) -> Expr -> a
fold alg = go
  where
  go = alg . fmap go . out
