{-# LANGUAGE UndecidableInstances #-}
module Facet.Surface
( -- * Types
  Kind(..)
, Type(..)
, Mul(..)
  -- * Expressions
, Expr(..)
, Interface(..)
, Clause(..)
  -- * Patterns
, Pattern(..)
, ValPattern(..)
, EffPattern(..)
  -- * Definitions
, Def(..)
  -- * Modules
, Module(..)
, Import(..)
  -- * Annotations
, Ann(..)
, ann_
, comments_
, out_
, annUnary
, annBinary
, Comment(..)
) where

import Control.Lens (Lens, Lens', lens)
import Data.Function (on)
import Data.Text (Text)
import Facet.Name
import Facet.Snoc
import Facet.Span
import Facet.Syntax

-- Types

data Kind
  = KType
  | KInterface
  | KArrow (Maybe Name) (Ann Kind) (Ann Kind)
  deriving (Eq, Show)

data Type
  = TVar QName
  | TString
  | TForAll Name (Ann Kind) (Ann Type)
  | TArrow (Maybe Name) (Maybe Mul) (Ann Type) (Ann Type)
  | TComp [Ann Interface] (Ann Type)
  | TApp (Ann Type) (Ann Type)
  deriving (Eq, Show)

data Mul = Zero | One
  deriving (Bounded, Enum, Eq, Ord, Show)


-- Expressions

data Expr
  = Var QName
  | Hole Name
  | Lam [Clause]
  | App (Ann Expr) (Ann Expr)
  | As (Ann Expr) (Ann Type)
  | String Text
  deriving (Eq, Show)


data Interface = Interface (Ann QName) (Snoc (Ann Type))
  deriving (Eq, Show)


data Clause = Clause (Ann Pattern) (Ann Expr)
  deriving (Eq, Show)


-- Patterns

data Pattern
  = PVal (Ann ValPattern)
  | PEff (Ann EffPattern)
  deriving (Eq, Show)

data ValPattern
  = PWildcard
  | PVar Name
  | PCon QName [Ann ValPattern]
  deriving (Eq, Show)

data EffPattern = POp QName [Ann ValPattern] (Ann ValPattern)
  deriving (Eq, Show)


-- Declarations

data Def
  = DataDef [Ann (Name ::: Ann Type)] (Ann Kind)
  | InterfaceDef [Ann (Name ::: Ann Type)] (Ann Kind)
  | TermDef (Ann Expr) (Ann Type)
  deriving (Eq, Show)


-- Modules

data Module = Module
  { name      :: MName
  , imports   :: [Ann Import]
  -- FIXME: store source references for operators’ definitions, for error reporting
  , operators :: [(Op, Assoc)]
  , defs      :: [Ann (Name, Ann Def)]
  }
  deriving (Eq, Show)


newtype Import = Import { name :: MName }
  deriving (Eq, Show)


-- Annotations

data Ann a = Ann
  { ann      :: Span
  , comments :: Snoc (Span, Comment)
  , out      :: a
  }
  deriving (Foldable, Functor, Traversable)

instance Eq a => Eq (Ann a) where
  (==) = (==) `on` out

instance Ord a => Ord (Ann a) where
  compare = compare `on` out

instance Show a => Show (Ann a) where
  showsPrec p = showsPrec p . out

instance HasSpan (Ann a) where
  span_ = ann_

ann_ :: Lens' (Ann a) Span
ann_ = lens ann (\ a ann -> a{ ann })

comments_ :: Lens' (Ann a) (Snoc (Span, Comment))
comments_ = lens comments (\ a comments -> a{ comments })

out_ :: Lens (Ann a) (Ann b) a b
out_ = lens out (\ a out -> a{ out })


annUnary :: (Ann a -> a) -> Ann a -> Ann a
annUnary f a = Ann (ann a) Nil (f a)

annBinary :: (Ann a -> Ann b -> a) -> Ann a -> Ann b -> Ann a
annBinary f a b = Ann (ann a <> ann b) Nil (f a b)


newtype Comment = Comment { getComment :: Text }
  deriving (Eq, Show)
