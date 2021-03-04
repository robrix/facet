{-# LANGUAGE OverloadedStrings #-}
module Facet.Elab.Type
( -- * Types
  _Type
, _Interface
, _String
, forAll
, elabKind
, elabType
, elabPosType
, elabNegType
  -- * Judgements
, IsType(..)
, mapIsType
) where

import           Control.Algebra
import           Control.Effect.Lens (views)
import           Control.Effect.State
import           Control.Effect.Throw
import           Control.Effect.Writer
import           Data.Bifunctor (first)
import           Data.Foldable (foldl')
import           Data.Functor (($>))
import           Facet.Context
import           Facet.Core.Module
import           Facet.Core.Type
import           Facet.Elab
import           Facet.Name
import           Facet.Semiring (Few(..), one, zero, (><<))
import qualified Facet.Surface as S
import           Facet.Syntax
import           Facet.Usage (Usage)
import           GHC.Stack

var :: (HasCallStack, Has (Throw Err) sig m) => (Var Meta Index -> a) -> QName -> Synth m a
var mk n = Synth $ views context_ (lookupInContext n) >>= \case
  Just (i, q, _T) -> use i q $> (mk (Free i) ::: _T)
  _               -> do
    q :=: d <- resolveQ n
    _T <- case d of
      DData      _ _K -> pure _K
      DInterface _ _K -> pure _K
      _               -> freeVariable q
    pure $ mk (Global q) ::: _T


_Type :: Synth m TExpr
_Type = Synth $ pure $ TType ::: Type

_Interface :: Synth m TExpr
_Interface = Synth $ pure $ TInterface ::: Type

_String :: Synth m (Pos TExpr)
_String = Synth $ pure $ stringT ::: Type


forAll :: (HasCallStack, Has (Throw Err) sig m) => Name ::: Synth m TExpr -> Synth m (Neg TExpr) -> Synth m (Neg TExpr)
forAll (n ::: t) b = Synth $ do
  t' <- check (switch t ::: Type)
  env <- views context_ toEnv
  subst <- get
  let vt = eval subst (Left <$> env) t'
  b' <- Binding n zero vt |- check (switch b ::: Type)
  pure $ forAllT n t' b' ::: Type

arrow :: (HasCallStack, Has (Throw Err) sig m) => (a -> b -> c) -> Synth m a -> Synth m b -> Synth m c
arrow mk a b = Synth $ do
  a' <- check (switch a ::: Type)
  b' <- check (switch b ::: Type)
  pure $ mk a' b' ::: Type


comp :: (HasCallStack, Has (Throw Err) sig m) => [Synth m (Interface TExpr)] -> Synth m (Pos TExpr) -> Synth m (Neg TExpr)
comp s t = Synth $ do
  s' <- traverse (check . (::: Interface) . switch) s
  t' <- check (switch t ::: Type)
  pure $ compT s' t' ::: Type

app :: (HasCallStack, Has (Throw Err) sig m) => (a -> b -> c) -> Synth m a -> Synth m b -> Synth m c
app mk f a = Synth $ do
  f' ::: _F <- synth f
  (_ ::: (q, _A), _B) <- expectFunction "in application" _F
  -- FIXME: test _A for Comp and extend the sig
  a' <- censor @Usage (q ><<) $ check (switch a ::: _A)
  pure $ mk f' a' ::: _B


elabKind :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> Synth m TExpr
elabKind (S.Ann s _ e) = mapSynth (pushSpan s) $ case e of
  S.TArrow  n q a b -> arrow (TArrow n (maybe Many interpretMul q)) (elabKind a) (elabKind b)
  S.TApp f a        -> app TApp (elabKind f) (elabKind a)
  S.TVar n          -> var TVar n
  S.KType           -> _Type
  S.KInterface      -> _Interface
  S.TComp{}         -> nope
  S.TForAll{}       -> nope
  S.TString         -> nope
  where
  nope = Synth $ couldNotSynthesize (show e <> " at the kind level")

elabType :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> Synth m (Either (Neg TExpr) (Pos TExpr))
elabType (S.Ann s _ e) = mapSynth (pushSpan s) $ case e of
  S.TForAll n t b   -> Left <$> forAll (n ::: elabKind t) (elabNegType b)
  S.TArrow  n q a b -> Left <$> arrow (arrowT n (maybe Many interpretMul q)) (elabPosType a) (elabNegType b)
  S.TComp s t       -> Left <$> comp (map synthInterface s) (elabPosType t)
  S.TApp f a        -> Right <$> app appT (elabPosType f) (elabPosType a)
  S.TVar n          -> Right <$> var varT n
  S.TString         -> Right <$> _String
  S.KType           -> nope
  S.KInterface      -> nope
  where
  nope = Synth $ couldNotSynthesize (show e <> " at the type level")

elabPosType :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> Synth m (Pos TExpr)
elabPosType = fmap (either thunkT id) . elabType

elabNegType :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> Synth m (Neg TExpr)
elabNegType = fmap (either id (compT [])) . elabType


interpretMul :: S.Mul -> Few
interpretMul = \case
  S.Zero -> zero
  S.One  -> one


synthInterface :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Interface -> Synth m (Interface TExpr)
synthInterface (S.Ann s _ (S.Interface (S.Ann sh _ h) sp)) = mapSynth (pushSpan s) . fmap IInterface $
  foldl' (app TApp) (mapSynth (pushSpan sh) (var TVar h)) (elabKind <$> sp)


newtype IsType m a = IsType { isType :: Elab m (a ::: Type) }

instance Functor (IsType m) where
  fmap f (IsType m) = IsType (first f <$> m)

mapIsType :: (Elab m (a ::: Type) -> Elab m (b ::: Type)) -> IsType m a -> IsType m b
mapIsType f = IsType . f . isType
