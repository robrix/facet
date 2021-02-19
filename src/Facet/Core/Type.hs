module Facet.Core.Type
( -- * Types
  Type(..)
, CType(..)
, VType(..)
, global
, free
, metavar
, unRet
, occursIn
  -- ** Elimination
, ($$)
, ($$*)
, ($$$)
, ($$$*)
  -- ** Debugging
, showType
  -- * Type expressions
, TExpr(..)
, CTExpr(..)
, VTExpr(..)
  -- * Quotation
, quote
, quoteC
, quoteV
, eval
, evalC
, evalV
  -- * Substitution
, Subst(..)
, insert
, lookupMeta
, solveMeta
, declareMeta
, metas
) where

import           Control.Effect.Empty
import           Data.Either (fromLeft)
import           Data.Foldable (foldl')
import           Data.Function ((&))
import qualified Data.IntMap as IntMap
import           Facet.Name
import           Facet.Semiring
import           Facet.Show
import           Facet.Snoc
import           Facet.Syntax
import           Facet.Usage
import           GHC.Stack
import           Prelude hiding (lookup)

-- Types

data Type
  = VType
  | VInterface
  | VString
  | VForAll Name Type (Type -> Type)
  | VArrow (Maybe Name) Quantity Type Type
  | VNe (Var Meta Level) (Snoc Type) (Snoc Type)
  | VComp [Type] Type
  | VF Type
  | VU Type

data CType
  = ForAll Name CType (VType -> CType)
  | Arrow (Maybe Name) Quantity VType CType
  | Comp [CType] CType
  | Ne (Var Meta Level) (Snoc VType) (Snoc VType)
  | F VType

data VType
  = Var (Var Meta Level)
  | Type
  | Interface
  | String
  | U CType


global :: Q Name -> Type
global = var . Global

free :: Level -> Type
free = var . Free

metavar :: Meta -> Type
metavar = var . Metavar


var :: Var Meta Level -> Type
var v = VNe v Nil Nil


unRet :: Has Empty sig m => Type -> m ([Type], Type)
unRet = \case
  VComp sig _T -> pure (sig, _T)
  _T           -> empty


occursIn :: (Var Meta Level -> Bool) -> Level -> Type -> Bool
occursIn p = go
  where
  go d = \case
    VType          -> False
    VInterface     -> False
    VForAll _ t b  -> go d t || go (succ d) (b (free d))
    VArrow _ _ a b -> go d a || go d b
    VComp s t      -> any (go d) s || go d t
    VNe h ts sp    -> p h || any (go d) ts || any (go d) sp
    VString        -> False
    VF t           -> go d t
    VU t           -> go d t


-- Elimination

($$) :: HasCallStack => Type -> Type -> Type
VNe h ts es $$ a = VNe h ts (es :> a)
_           $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: (HasCallStack, Foldable t) => Type -> t Type -> Type
($$*) = foldl' ($$)

infixl 9 $$, $$*

($$$) :: HasCallStack => Type -> Type -> Type
VNe h ts es   $$$ t = VNe h (ts :> t) es
VForAll _ _ b $$$ t = b t
_             $$$ _ = error "can’t apply non-neutral/forall type"

($$$*) :: (HasCallStack, Foldable t) => Type -> t Type -> Type
($$$*) = foldl' ($$)

infixl 9 $$$, $$$*


app :: HasCallStack => CType -> VType -> CType
app (Ne h ts es) a = Ne h ts (es :> a)
app _            _ = error "can’t apply non-neutral/forall type"

inst :: HasCallStack => CType -> VType -> CType
inst (Ne h ts es)   t = Ne h (ts :> t) es
inst (ForAll _ _ b) t = b t
inst _              _ = error "can’t apply non-neutral/forall type"


-- Debugging

showType :: Snoc ShowP -> Type -> ShowP
showType env = \case
  VType         -> string "Type"
  VInterface    -> string "Interface"
  VForAll n t b -> prec 0 $ brace (name n <+> char ':' <+> setPrec 0 (showType env t)) <+> string "->" <+> setPrec 0 (showType (env :> name n) (b (free (Level (length env)))))
  VArrow n q t b  -> case n of
    Just  n -> paren (name n <+> char ':' <+> mult q (showType env t)) <+> string "->" <+> setPrec 0 (showType env b)
    Nothing -> setPrec 1 (mult q (showType env t)) <+> string "->" <+> setPrec 0 (showType env b)
  VNe f ts as   -> head f $$* (brace . showType env <$> ts) $$* (setPrec 11 . showType env <$> as)
  VComp s t     -> sig s <+> showType env t
  VString       -> string "String"
  VF t          -> showType env t
  VU t          -> showType env t
  where
  sig s = bracket (commaSep (map (showType env) s))
  ($$*) = foldl' (\ f a -> prec 10 (f <+> a))
  infixl 9 $$*
  head = \case
    Global q  -> qname q
    Free v    -> env ! getIndex (levelToIndex (Level (length env)) v)
    Metavar m -> char '?' <> string (show (getMeta m))
  mult q = if
    | q == zero -> (char '0' <+>)
    | q == one  -> (char '1' <+>)
    | otherwise -> id


-- Type expressions

data TExpr
  = TType
  | TInterface
  | TString
  | TVar (Var Meta Index)
  | TForAll Name TExpr TExpr
  | TArrow (Maybe Name) Quantity TExpr TExpr
  | TComp [TExpr] TExpr
  | TInst TExpr TExpr
  | TApp TExpr TExpr
  | TF TExpr
  | TU TExpr
  deriving (Eq, Ord, Show)

data CTExpr
  = CXForAll Name CTExpr CTExpr
  | CXArrow (Maybe Name) Quantity VTExpr CTExpr
  | CXComp [CTExpr] CTExpr
  | CXInst CTExpr VTExpr
  | CXApp CTExpr VTExpr
  | CXF VTExpr
  deriving (Eq, Ord, Show)

data VTExpr
  = VXType
  | VXInterface
  | VXString
  | VXVar (Var Meta Index)
  | VXU CTExpr
  deriving (Eq, Ord, Show)


-- Quotation

quote :: Level -> Type -> TExpr
quote d = \case
  VType          -> TType
  VInterface     -> TInterface
  VString        -> TString
  VForAll n t b  -> TForAll n (quote d t) (quote (succ d) (b (free d)))
  VArrow n q a b -> TArrow n q (quote d a) (quote d b)
  VComp s t      -> TComp (quote d <$> s) (quote d t)
  VNe n ts sp    -> foldl' (&) (foldl' (&) (TVar (levelToIndex d <$> n)) (flip TInst . quote d <$> ts)) (flip TApp . quote d <$> sp)
  VF t           -> TF (quote d t)
  VU t           -> TU (quote d t)

quoteC :: Level -> CType -> CTExpr
quoteC d = \case
  ForAll n t b  -> CXForAll n (quoteC d t) (quoteC (succ d) (b (Var (Free d))))
  Arrow n q a b -> CXArrow n q (quoteV d a) (quoteC d b)
  Comp s t      -> CXComp (quoteC d <$> s) (quoteC d t)
  Ne n ts sp    -> foldl' (&) (foldl' (&) (CXF (VXVar (levelToIndex d <$> n))) (flip CXInst . quoteV d <$> ts)) (flip CXApp . quoteV d <$> sp)
  F t           -> CXF (quoteV d t)

quoteV :: Level -> VType -> VTExpr
quoteV d = \case
  Var n     -> VXVar (levelToIndex d <$> n)
  Type      -> VXType
  Interface -> VXInterface
  String    -> VXString
  U t       -> VXU (quoteC d t)

eval :: HasCallStack => Subst Type -> Snoc (Either Type a) -> TExpr -> Type
eval subst = go where
  go env = \case
    TType            -> VType
    TInterface       -> VInterface
    TString          -> VString
    TVar (Global n)  -> global n
    TVar (Free v)    -> fromLeft (error ("term variable at index " <> show v)) (env ! getIndex v)
    TVar (Metavar m) -> maybe (metavar m) tm (lookupMeta m subst)
    TForAll n t b    -> VForAll n (go env t) (\ v -> go (env :> Left v) b)
    TArrow n q a b   -> VArrow n q (go env a) (go env b)
    TComp s t        -> VComp (go env <$> s) (go env t)
    TInst f a        -> go env f $$$ go env a
    TApp  f a        -> go env f $$  go env a
    TF t             -> VF (go env t)
    TU t             -> VU (go env t)

evalC :: HasCallStack => Subst VType -> Snoc (Either VType a) -> CTExpr -> CType
evalC subst = go where
  go env = \case
    CXForAll n t b  -> ForAll n (go env t) (\ v -> go (env :> Left v) b)
    CXArrow n q a b -> Arrow n q (evalV subst env a) (go env b)
    CXComp s t      -> Comp (go env <$> s) (go env t)
    CXInst f a      -> go env f `inst` evalV subst env a
    CXApp  f a      -> go env f `app`  evalV subst env a
    CXF t           -> F (evalV subst env t)

evalV :: HasCallStack => Subst VType -> Snoc (Either VType a) -> VTExpr -> VType
evalV subst = go where
  go env = \case
    VXType            -> Type
    VXInterface       -> Interface
    VXString          -> String
    VXVar (Global n)  -> Var (Global n)
    VXVar (Free v)    -> fromLeft (error ("term variable at index " <> show v)) (env ! getIndex v)
    VXVar (Metavar m) -> maybe (Var (Metavar m)) tm (lookupMeta m subst)
    VXU t             -> U (evalC subst env t)


-- Substitution

newtype Subst t = Subst (IntMap.IntMap (Maybe t ::: t))
  deriving (Monoid, Semigroup)

insert :: Meta -> Maybe t ::: t -> Subst t -> Subst t
insert (Meta i) t (Subst metas) = Subst (IntMap.insert i t metas)

lookupMeta :: Meta -> Subst t -> Maybe (t ::: t)
lookupMeta (Meta i) (Subst metas) = do
  v ::: _T <- IntMap.lookup i metas
  (::: _T) <$> v

solveMeta :: Meta -> t -> Subst t -> Subst t
solveMeta (Meta i) t (Subst metas) = Subst (IntMap.update (\ (_ ::: _T) -> Just (Just t ::: _T)) i metas)

declareMeta :: t -> Subst t -> (Subst t, Meta)
declareMeta _K (Subst metas) = (Subst (IntMap.insert v (Nothing ::: _K) metas), Meta v) where
  v = maybe 0 (succ . fst . fst) (IntMap.maxViewWithKey metas)

metas :: Subst t -> [Meta :=: Maybe t ::: t]
metas (Subst metas) = map (\ (k, v) -> Meta k :=: v) (IntMap.toList metas)
