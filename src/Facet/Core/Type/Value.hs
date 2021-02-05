module Facet.Core.Type.Value
( -- * Value types
  VType(..)
  -- * Computation types
, CType(..)
) where

import Facet.Core.Type.Expr
import Facet.Name
import Facet.Stack
import Facet.Usage

-- Value types

data VType


-- Computation types

data CType
  = CForAll Name CType (CType -> CType)
  | CArrow (Maybe Name) Quantity CType CType
  | CNe (TVar Level) (Stack CType) (Stack CType)
  | CRet [CType] VType
