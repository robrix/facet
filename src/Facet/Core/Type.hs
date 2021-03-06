module Facet.Core.Type
( -- * Types
  Sorted(..)
, unSTerm
, unSType
, Interface(..)
, Kind(..)
, kglobal
, kapp
, NType(..)
, PType(..)
, global
, free
, metavar
, unComp
, unThunk
, occursInN
, occursInP
  -- * Type expressions
, NTExpr(..)
, PTExpr(..)
  -- ** Type eliminators
, unarrowT
, uncompT
, unthunkT
  -- * Quotation
, quoteN
, quoteP
, evalN
, evalP
) where

import Control.Effect.Empty
import Data.Either (fromLeft)
import Data.Foldable (foldl')
import Facet.Name
import Facet.Snoc
import Facet.Subst
import Facet.Syntax
import Facet.Usage
import GHC.Stack
import Prelude hiding (lookup)

-- Types

data Sorted
  = STerm PType
  | SType Kind

unSTerm :: Has Empty sig m => Sorted -> m PType
unSTerm = \case{ STerm ty -> pure ty ; _ -> empty }

unSType :: Has Empty sig m => Sorted -> m Kind
unSType = \case{ SType ki -> pure ki ; _ -> empty }


-- FIXME: this doesn’t accommodate type parameters.
newtype Interface = IInterface { getInterface :: Kind }
  deriving (Eq, Ord, Show)

data Kind
  = Type
  | Interface
  | KArrow (Maybe Name) Kind Kind
  | KSpine QName (Snoc Kind)
  deriving (Eq, Ord, Show)

kglobal :: QName -> Kind
kglobal n = KSpine n Nil

kapp :: Kind -> Kind -> Kind
kapp (KSpine h as) a = KSpine h (as :> a)
kapp _             _ = error "invalid kind application"


data NType
  = Arrow (Maybe Name) Quantity PType NType
  | Comp [Interface] PType

data PType
  = ForAll Name Kind (PType -> PType)
  | Ne (Var Meta Level) (Snoc PType)
  | String
  | Thunk NType


global :: QName -> PType
global n = Ne (Global n) Nil

free :: Level -> PType
free l = Ne (Free l) Nil

metavar :: Meta -> PType
metavar m = Ne (Metavar m) Nil


unComp :: Has Empty sig m => NType -> m ([Interface], PType)
unComp = \case
  Comp sig _T -> pure (sig, _T)
  _T          -> empty

unThunk :: Has Empty sig m => PType -> m NType
unThunk = \case
  Thunk t -> pure t
  _       -> empty


occursInN :: Meta -> Level -> NType -> Bool
occursInN = fst . occursIn

occursInP :: Meta -> Level -> PType -> Bool
occursInP = snd . occursIn

occursIn :: Meta -> (Level -> NType -> Bool, Level -> PType -> Bool)
occursIn v = (goN, goP)
  where
  goN :: Level -> NType -> Bool
  goN d = \case
    Arrow _ _ a b -> goP d a || goN d b
    Comp _ t      -> goP d t
  goP :: Level -> PType -> Bool
  goP d = \case
    ForAll  _ _ b -> goP (succ d) (b (free d))
    Ne h sp       -> Metavar v == h || any (goP d) sp
    String        -> False
    Thunk t       -> goN d t



-- Elimination

app :: HasCallStack => PType -> PType -> PType
app (Ne h es) a = Ne h (es :> a)
app _         _ = error "can’t apply non-neutral/forall type"


-- Type expressions

data NTExpr
  = TArrow (Maybe Name) Quantity PTExpr NTExpr
  | TComp [Interface] PTExpr
  deriving (Eq, Ord, Show)

data PTExpr
  = TForAll Name Kind PTExpr
  | TVar (Var Meta Index)
  | TApp PTExpr PTExpr
  | TString
  | TThunk NTExpr
  deriving (Eq, Ord, Show)


-- Type eliminators

unarrowT :: Has Empty sig m => NTExpr -> m (Maybe Name, Quantity, PTExpr, NTExpr)
unarrowT = \case
  TArrow n q a b -> pure (n, q, a, b)
  _              -> empty

uncompT :: Has Empty sig m => NTExpr -> m ([Interface], PTExpr)
uncompT = \case
  TComp sig _T -> pure (sig, _T)
  _            -> empty

unthunkT :: Has Empty sig m => PTExpr -> m NTExpr
unthunkT = \case
  TThunk _T -> pure _T
  _         -> empty


-- Quotation

quoteN :: Level -> NType -> NTExpr
quoteN d = \case
  Arrow n q a b -> TArrow n q (quoteP d a) (quoteN d b)
  Comp s t      -> TComp s (quoteP d t)

quoteP :: Level -> PType -> PTExpr
quoteP d = \case
  ForAll n t b -> TForAll n t (quoteP (succ d) (b (free d)))
  Ne n sp      -> foldl' TApp (TVar (levelToIndex d <$> n)) (quoteP d <$> sp)
  String       -> TString
  Thunk t      -> TThunk (quoteN d t)

evalN :: HasCallStack => Subst PType Kind -> Snoc (Either PType a) -> NTExpr -> NType
evalN = fst . eval

evalP :: HasCallStack => Subst PType Kind -> Snoc (Either PType a) -> PTExpr -> PType
evalP = snd . eval

eval :: HasCallStack => Subst PType Kind -> (Snoc (Either PType a) -> NTExpr -> NType, Snoc (Either PType a) -> PTExpr -> PType)
eval subst = (goN, goP) where
  goN :: Snoc (Either PType a) -> NTExpr -> NType
  goN env = \case
    TArrow n q a b -> Arrow n q (goP env a) (goN env b)
    TComp s t      -> Comp s (goP env t)
  goP :: Snoc (Either PType a) -> PTExpr -> PType
  goP env = \case
    TForAll n t b    -> ForAll n t (\ v -> goP (env :> Left v) b)
    TApp f a         -> goP env f `app` goP env a
    TString          -> String
    TVar (Global n)  -> global n
    TVar (Free v)    -> fromLeft (error ("term variable at index " <> show v)) (env ! getIndex v)
    TVar (Metavar m) -> maybe (metavar m) tm (lookupMeta m subst)
    TThunk t         -> Thunk (goN env t)
