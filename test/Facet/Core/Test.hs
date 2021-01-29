{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module Facet.Core.Test
( tests
) where

import Facet.Core
import Facet.Name
import Facet.Stack
import Hedgehog hiding (Var, eval)

tests :: IO Bool
tests = checkParallel $$(discover)

prop_quotation_inverse = property $ do
  let init = TForAll (U "A") TType (TArrow (Just (U "x")) (TVar (Free 0)) (TComp [] (TVar (Free 1))))
  quote 0 (eval Nil mempty init) === init
