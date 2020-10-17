{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Env
( Env(..)
, fromList
, lookup
, insert
) where

import           Control.Monad (guard)
import           Data.List (uncons)
import qualified Data.Map as Map
import           Facet.Name
import           Facet.Syntax
import           Prelude hiding (lookup)

newtype Env a = Env { getEnv :: Map.Map DName (Map.Map MName (Maybe a ::: a)) }
  deriving (Monoid, Semigroup)

fromList :: [(DName, MName :=: Maybe a ::: a)] -> Env a
fromList = Env . Map.fromListWith (<>) . map (fmap (\ (mn :=: t) -> Map.singleton mn t))

lookup :: DName -> Env a -> Maybe (MName :=: Maybe a ::: a)
lookup k (Env env) = do
  mod <- Map.lookup k env
  ((mn, v), t) <- uncons (Map.toList mod)
  (mn :=: v) <$ guard (null t)

insert :: QName :=: Maybe a ::: a -> Env a -> Env a
insert (m :.: d :=: v) = Env . Map.insertWith (<>) d (Map.singleton m v) . getEnv
