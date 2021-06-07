{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module Facet.Core.Type.Test
( tests
) where

import Facet.Env
import Facet.Kind
import Facet.Name
import Facet.Semiring
import Facet.Syntax
import Facet.Type.Expr
import Facet.Type.Norm (eval, quote)
import Hedgehog hiding (Var, eval)

tests :: IO Bool
tests = checkParallel $$(discover)

prop_quotation_inverse = property $ do
  let init = ForAll (U "A") KType (Arrow (Just (U "x")) Many (Var (Free (Right (LName 0 (U "A"))))) (Comp mempty (Var (Free (Right (LName 0 (U "A")))))))
  quote 0 (eval mempty empty init) === init
