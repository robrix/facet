module Facet.Core.Type
( -- * Types
  Type(..)
, CType(..)
, global
, free
, metavar
, var
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
, VTExpr(..)
, CTExpr(..)
  -- * Quotation
, quote
, eval
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
import           Facet.Core.Type.Expr
import           Facet.Core.Type.Value
import           Facet.Name
import           Facet.Semiring
import           Facet.Show
import           Facet.Stack
import           Facet.Syntax
import           Facet.Usage
import           GHC.Stack
import           Prelude hiding (lookup)

-- Types

data Type
  = VKType
  | VKInterface
  | VTForAll Name Type (Type -> Type)
  | VTArrow (Maybe Name) Quantity Type Type
  | VTNe (Var Meta Level) (Stack Type) (Stack Type)
  | VTSusp Type
  | VTRet [Type] Type
  | VTString


global :: Q Name -> Type
global = var . Global

free :: Level -> Type
free = var . Free

metavar :: Meta -> Type
metavar = var . Metavar


var :: Var Meta Level -> Type
var v = VTNe v Nil Nil


unRet :: Has Empty sig m => Type -> m ([Type], Type)
unRet = \case
  VTRet sig _T -> pure (sig, _T)
  _T           -> empty


occursIn :: (Var Meta Level -> Bool) -> Level -> Type -> Bool
occursIn p = go
  where
  go d = \case
    VKType          -> False
    VKInterface     -> False
    VTForAll _ t b  -> go d t || go (succ d) (b (free d))
    VTArrow _ _ a b -> go d a || go d b
    VTSusp t        -> go d t
    VTRet s t       -> any (go d) s || go d t
    VTNe h ts sp    -> p h || any (go d) ts || any (go d) sp
    VTString        -> False


-- Elimination

($$) :: HasCallStack => Type -> Type -> Type
VTNe h ts es $$ a = VTNe h ts (es :> a)
_            $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: (HasCallStack, Foldable t) => Type -> t Type -> Type
($$*) = foldl' ($$)

infixl 9 $$, $$*

($$$) :: HasCallStack => Type -> Type -> Type
VTNe h ts es   $$$ t = VTNe h (ts :> t) es
VTForAll _ _ b $$$ t = b t
_              $$$ _ = error "can’t apply non-neutral/forall type"

($$$*) :: (HasCallStack, Foldable t) => Type -> t Type -> Type
($$$*) = foldl' ($$)

infixl 9 $$$, $$$*


-- Debugging

showType :: Stack ShowP -> Type -> ShowP
showType env = \case
  VKType         -> string "Type"
  VKInterface    -> string "Interface"
  VTForAll n t b -> prec 0 $ brace (name n <+> char ':' <+> setPrec 0 (showType env t)) <+> string "->" <+> setPrec 0 (showType (env :> name n) (b (free (Level (length env)))))
  VTArrow n q t b  -> case n of
    Just  n -> paren (name n <+> char ':' <+> mult q (showType env t)) <+> string "->" <+> setPrec 0 (showType env b)
    Nothing -> setPrec 1 (mult q (showType env t)) <+> string "->" <+> setPrec 0 (showType env b)
  VTNe f ts as   -> head f $$* (brace . showType env <$> ts) $$* (setPrec 11 . showType env <$> as)
  VTSusp t       -> brace (showType env t)
  VTRet s t      -> sig s <+> showType env t
  VTString       -> string "String"
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
  = TVar (Var Meta Index)
  | TType
  | TInterface
  | TString
  | TForAll Name TExpr TExpr
  | TArrow (Maybe Name) Quantity TExpr TExpr
  | TSusp TExpr
  | TRet [TExpr] TExpr
  | TInst TExpr TExpr
  | TApp TExpr TExpr
  deriving (Eq, Ord, Show)


-- Quotation

quote :: Level -> Type -> TExpr
quote d = \case
  VKType          -> TType
  VKInterface     -> TInterface
  VTForAll n t b  -> TForAll n (quote d t) (quote (succ d) (b (free d)))
  VTArrow n q a b -> TArrow n q (quote d a) (quote d b)
  VTSusp t        -> TSusp (quote d t)
  VTRet s t       -> TRet (quote d <$> s) (quote d t)
  VTNe n ts sp    -> foldl' (&) (foldl' (&) (TVar (levelToIndex d <$> n)) (flip TInst . quote d <$> ts)) (flip TApp . quote d <$> sp)
  VTString        -> TString

eval :: HasCallStack => Subst -> Stack (Either Type a) -> TExpr -> Type
eval subst = go where
  go env = \case
    TVar (Global n)  -> global n
    TVar (Free v)    -> fromLeft (error ("term variable at index " <> show v)) (env ! getIndex v)
    TVar (Metavar m) -> maybe (metavar m) tm (lookupMeta m subst)
    TType            -> VKType
    TInterface       -> VKInterface
    TForAll n t b    -> VTForAll n (go env t) (\ v -> go (env :> Left v) b)
    TArrow n q a b   -> VTArrow n q (go env a) (go env b)
    TSusp t          -> VTSusp (go env t)
    TRet s t         -> VTRet (go env <$> s) (go env t)
    TInst f a        -> go env f $$$ go env a
    TApp  f a        -> go env f $$  go env a
    TString          -> VTString


-- Substitution

newtype Subst = Subst (IntMap.IntMap (Maybe Type ::: Type))
  deriving (Monoid, Semigroup)

insert :: Meta -> Maybe Type ::: Type -> Subst -> Subst
insert (Meta i) t (Subst metas) = Subst (IntMap.insert i t metas)

lookupMeta :: Meta -> Subst -> Maybe (Type ::: Type)
lookupMeta (Meta i) (Subst metas) = do
  v ::: _T <- IntMap.lookup i metas
  (::: _T) <$> v

solveMeta :: Meta -> Type -> Subst -> Subst
solveMeta (Meta i) t (Subst metas) = Subst (IntMap.update (\ (_ ::: _T) -> Just (Just t ::: _T)) i metas)

declareMeta :: Type -> Subst -> (Subst, Meta)
declareMeta _K (Subst metas) = (Subst (IntMap.insert v (Nothing ::: _K) metas), Meta v) where
  v = maybe 0 (succ . fst . fst) (IntMap.maxViewWithKey metas)

metas :: Subst -> [Meta :=: Maybe Type ::: Type]
metas (Subst metas) = map (\ (k, v) -> Meta k :=: v) (IntMap.toList metas)
