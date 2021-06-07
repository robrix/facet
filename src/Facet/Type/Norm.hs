{-# LANGUAGE ImportQualifiedPost #-}
module Facet.Type.Norm
( -- * Types
  Type(..)
, global
, free
, metavar
, unNeutral
, unComp
, Classifier(..)
, Classified(..)
, occursIn
  -- ** Elimination
, ($$)
, ($$*)
  -- * Quotation
, quote
, eval
, apply
) where

import           Control.Effect.Empty
import           Control.Lens (Prism', prism')
import           Data.Foldable (foldl')
import           Data.Function (on, (&))
import           Data.Maybe (fromMaybe)
import           Facet.Env hiding (empty)
import           Facet.Interface
import           Facet.Kind
import           Facet.Name
import           Facet.Pattern
import           Facet.Snoc
import           Facet.Subst
import           Facet.Syntax
import           Facet.Type
import qualified Facet.Type.Expr as TX
import           Facet.Usage hiding (singleton)
import           GHC.Stack
import           Prelude hiding (lookup)

-- Types

data Type
  = String
  | ForAll Name Kind (Type -> Type)
  | Arrow (Maybe Name) Quantity Type Type
  | Ne (Var (Either Meta (LName Level))) (Snoc Type)
  | Comp (Signature Type) Type

instance Eq Type where
  (==) = (==) `on` quote 0

instance Ord Type where
  compare = compare `on` quote 0

instance TType (T Type) where
  string = T String
  forAll n (T k) b = T (ForAll n k (getT . b . T))
  arrow n q (T a) (T b) = T (Arrow n q a b)
  comp sig (T b) = T (Comp (mapSignature getT sig) b)
  app (T a) (T b) = T (a $$ b)


global :: RName -> Type
global = var . Global

free :: LName Level -> Type
free = var . Free . Right

metavar :: Meta -> Type
metavar = var . Free . Left


var :: Var (Either Meta (LName Level)) -> Type
var v = Ne v Nil


unNeutral :: Has Empty sig m => Type -> m (Var (Either Meta (LName Level)), Snoc Type)
unNeutral = \case
  Ne h sp -> pure (h, sp)
  _       -> empty

unComp :: Has Empty sig m => Type -> m (Signature Type, Type)
unComp = \case
  Comp sig _T -> pure (sig, _T)
  _T          -> empty


data Classifier
  = CK Kind
  | CT Type

class Classified t where
  classified :: Prism' Classifier t

instance Classified Kind where
  classified = prism' CK (\case{ CK _K -> pure _K ; _ -> empty })

instance Classified Type where
  classified = prism' CT (\case{ CT _T -> pure _T ; _ -> empty })


occursIn :: Meta -> Level -> Type -> Bool
occursIn p = go
  where
  go d = \case
    ForAll n _ b  -> go (succ d) (b (free (LName d n)))
    Arrow _ _ a b -> go d a || go d b
    Comp s t      -> any (go d) s || go d t
    Ne h sp       -> any (either (== p) (const False)) h || any (go d) sp
    String        -> False


-- Elimination

($$) :: HasCallStack => Type -> Type -> Type
Ne h es $$ a = Ne h (es :> a)
_       $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: (HasCallStack, Foldable t) => Type -> t Type -> Type
($$*) = foldl' ($$)

infixl 9 $$, $$*


-- Quotation

quote :: Level -> Type -> TX.Type
quote d = \case
  String        -> TX.String
  ForAll n t b  -> TX.ForAll n t (quote (succ d) (b (free (LName d n))))
  Arrow n q a b -> TX.Arrow n q (quote d a) (quote d b)
  Comp s t      -> TX.Comp (mapSignature (quote d) s) (quote d t)
  Ne n sp       -> foldl' (&) (TX.Var (fmap (fmap (levelToIndex d)) <$> n)) (flip TX.App . quote d <$> sp)

eval :: HasCallStack => Subst Type -> Env Type -> TX.Type -> Type
eval subst = go where
  go env = \case
    TX.String               -> String
    TX.Var (Global n)       -> global n
    TX.Var (Free (Right n)) -> index env n
    TX.Var (Free (Left m))  -> fromMaybe (metavar m) (lookupMeta m subst)
    TX.ForAll n t b         -> ForAll n t (\ _T -> go (env |> PVar (n :=: _T)) b)
    TX.Arrow n q a b        -> Arrow n q (go env a) (go env b)
    TX.Comp s t             -> Comp (mapSignature (go env) s) (go env t)
    TX.App  f a             -> go env f $$  go env a

apply :: HasCallStack => Subst Type -> Env Type -> Type -> Type
apply subst env = eval subst env . quote (level env)
