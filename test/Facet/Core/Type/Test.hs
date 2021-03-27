{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module Facet.Core.Type.Test
( tests
) where

import Facet.Core.Type
import Facet.Name
import Facet.Semiring
import Facet.Snoc
import Facet.Syntax
import Hedgehog hiding (Var, eval)

tests :: IO Bool
tests = checkParallel $$(discover)

prop_quotation_inverse = property $ do
  let init = TForAll (U "A") KType (TArrow (Just (U "x")) Many (TVar (Free (Right 0))) (TComp mempty (TVar (Free (Right 0)))))
  quote 0 (eval mempty Nil init) === init
