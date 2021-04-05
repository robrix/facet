module Facet.Term
( -- * Term expressions
  Expr(..)
) where

import           Data.Text (Text)
import           Facet.Name
import           Facet.Pattern
import           Facet.Syntax
import qualified Facet.Type.Expr as TX

-- Term expressions

data Expr
  = XVar (Var (LName Index))
  | XTLam Name Expr
  | XInst Expr TX.Type
  | XLam [(Pattern Name, Expr)]
  | XApp Expr Expr
  | XCon RName [Expr]
  | XString Text
  | XDict [RName :=: Expr]
  | XLet (Pattern Name) Expr Expr
  deriving (Eq, Ord, Show)
