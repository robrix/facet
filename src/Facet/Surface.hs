{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Surface
( -- * Expressions
  Expr(..)
, Type
, free
, qual
, Comp(..)
, Binding(..)
, Interface(..)
, Clause(..)
  -- * Patterns
, ValPattern(..)
, EffPattern(..)
  -- * Declarations
, Decl(..)
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
import Data.List.NonEmpty (NonEmpty)
import Data.Text (Text)
import Data.Void
import Facet.Name
import Facet.Span
import Facet.Stack
import Facet.Syntax

-- Expressions

data Expr a
  = Var MQName
  | Hole Name
  | KType
  | KInterface
  | TString
  | TComp (Ann (Comp a))
  | Lam [Clause a]
  | Thunk (Ann (Expr a))
  | Force (Ann (Expr a))
  | App (Ann (Expr a)) (Ann (Expr a))
  | As (Ann (Expr a)) (Ann (Type a))
  | String Text
  | M a
  deriving (Foldable, Functor, Traversable)

deriving instance Eq   a => Eq   (Expr a)
deriving instance Show a => Show (Expr a)

type Type = Expr


free :: Name -> Expr a
free = Var . (Nothing :?)

qual :: Q Name -> Expr a
qual (m :.: n) = Var (Just m :? n)


data Comp a = Comp
  { bindings :: [Ann (Binding a)]
  , delta    :: Maybe [Ann (Interface a)]
  , type'    :: Ann (Type a)
  }
  deriving (Foldable, Functor, Traversable)

deriving instance Eq   a => Eq   (Comp a)
deriving instance Show a => Show (Comp a)

data Binding a = Binding
  { pl    :: Pl
  -- | The names bound by this value. 'Nothing' indicates an unnamed binding (i.e. a regular old function type argument like @A -> B@), whereas 'Just' indicates one or more names are bound to a single type (e.g. a quantifier like @{ A, B : Type } -> C@).
  --
  -- This technically represents the same number of (total) cases as @[]@ would, but forces disjoint handling so we don’t accidentally e.g. bind or apply over a non-binding argument and truncate the list.
  , names :: Maybe (NonEmpty Name)
  -- | The signature, if any, provided at this position.
  --
  -- 'Nothing' indicates a value type; 'Just' with an empty list indicates a thunk with the ambient effects; 'Just' with one or more interfaces indicates that this position provides these effects. (Note that this can, in general, also hold signature variables.)
  , delta :: Maybe [Ann (Interface a)]
  , type' :: Ann (Type a)
  }
  deriving (Foldable, Functor, Traversable)

deriving instance Eq   a => Eq   (Binding a)
deriving instance Show a => Show (Binding a)


data Interface a = Interface (Ann MQName) (Stack (Ann (Type a)))
  deriving (Foldable, Functor, Traversable)

deriving instance Eq   a => Eq   (Interface a)
deriving instance Show a => Show (Interface a)


data Clause a = Clause (Ann (EffPattern a)) (Ann (Expr a))
  deriving (Foldable, Functor, Traversable)

deriving instance Eq   a => Eq   (Clause a)
deriving instance Show a => Show (Clause a)


-- Patterns

data ValPattern a
  = PWildcard
  | PVar Name
  | PCon MQName [Ann (ValPattern a)]
  deriving (Foldable, Functor, Traversable)

deriving instance Eq   a => Eq   (ValPattern a)
deriving instance Show a => Show (ValPattern a)

data EffPattern a
  = PEff MQName [Ann (ValPattern a)] Name
  -- | Catch-all effect pattern. Matches values and effect operations.
  | PAll Name
  | PVal (Ann (ValPattern a))
  deriving (Foldable, Functor, Traversable)

deriving instance Eq   a => Eq   (EffPattern a)
deriving instance Show a => Show (EffPattern a)


-- Declarations

data Decl a = Decl (Ann (Comp a)) (Def a)
  deriving (Foldable, Functor, Traversable)

deriving instance Eq   a => Eq   (Decl a)
deriving instance Show a => Show (Decl a)


data Def a
  = DataDef [Ann (Name ::: Ann (Comp a))]
  | InterfaceDef [Ann (Name ::: Ann (Comp a))]
  | TermDef (Ann (Expr a))
  deriving (Foldable, Functor, Traversable)

deriving instance Eq   a => Eq   (Def a)
deriving instance Show a => Show (Def a)



-- Modules

data Module a = Module
  { name      :: MName
  , imports   :: [Ann Import]
  -- FIXME: store source references for operators’ definitions, for error reporting
  , operators :: [(Op, Assoc)]
  , defs      :: [Ann (Name, Ann (Decl a))]
  }
  deriving (Foldable, Functor, Traversable)

deriving instance Eq   a => Eq   (Module a)
deriving instance Show a => Show (Module a)


newtype Import = Import { name :: MName }
  deriving (Eq, Show)


-- Annotations

data Ann a = Ann
  { ann      :: Span
  , comments :: Stack (Span, Comment)
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

comments_ :: Lens' (Ann a) (Stack (Span, Comment))
comments_ = lens comments (\ a comments -> a{ comments })

out_ :: Lens (Ann a) (Ann b) a b
out_ = lens out (\ a out -> a{ out })


annUnary :: (Ann (Expr Void) -> Expr Void) -> Ann (Expr Void) -> Ann (Expr Void)
annUnary f a = Ann (ann a) Nil (f a)

annBinary :: (Ann (Expr Void) -> Ann (Expr Void) -> Expr Void) -> Ann (Expr Void) -> Ann (Expr Void) -> Ann (Expr Void)
annBinary f a b = Ann (ann a <> ann b) Nil (f a b)


newtype Comment = Comment { getComment :: Text }
  deriving (Eq, Show)
