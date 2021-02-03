{-# LANGUAGE OverloadedStrings #-}
module Facet.Elab.Type
( -- * Types
  tvar
, _Type
, _Interface
, _String
, forAll
, (-->)
, comp
, synthType
, checkType
) where

import           Control.Algebra
import           Control.Effect.Lens (views)
import           Control.Effect.State
import           Control.Effect.Throw
import           Data.Foldable (foldl')
import           Facet.Context
import           Facet.Core.Type
import           Facet.Elab
import           Facet.Name
import           Facet.Semiring (Few(..), one, zero)
import qualified Facet.Surface as S
import           Facet.Syntax
import           GHC.Stack

tvar :: (HasCallStack, Has (Throw Err) sig m) => Q Name -> Synth m TExpr
tvar n = Synth $ views context_ (lookupInContext n) >>= \case
  Just (i, _T) -> pure $ TVar (TFree i) ::: _T
  Nothing      -> do
    q :=: _ ::: _T <- resolveQ n
    instantiate TInst $ TVar (TGlobal q) ::: _T


_Type :: Synth m TExpr
_Type = Synth $ pure $ TType ::: VKType

_Interface :: Synth m TExpr
_Interface = Synth $ pure $ TInterface ::: VKType

_String :: Synth m TExpr
_String = Synth $ pure $ TString ::: VKType


forAll :: (HasCallStack, Algebra sig m) => Name ::: Check m TExpr -> Check m TExpr -> Synth m TExpr
forAll (n ::: t) b = Synth $ do
  t' <- check (t ::: VKType)
  env <- views context_ toEnv
  subst <- get
  let vt = eval subst (Left <$> env) t'
  b' <- Binding n zero vt |- check (b ::: VKType)
  pure $ TForAll n t' b' ::: VKType

(-->) :: Either Name [Check m TExpr] ::: Check m (Quantity, TExpr) -> Check m TExpr -> Synth m TExpr
(n ::: a) --> b = Synth $ do
  n' <- traverse (traverse (\ e -> check (e ::: VKInterface))) n
  (q', a') <- check (a ::: VKType)
  b' <- check (b ::: VKType)
  pure $ TArrow n' q' a' b' ::: VKType

infixr 1 -->


comp :: [Check m TExpr] -> Check m TExpr -> Synth m TExpr
comp s t = Synth $ do
  s' <- traverse (check . (::: VKInterface)) s
  t' <- check (t ::: VKType)
  pure $ TComp s' t' ::: VKType


synthType :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> Synth m TExpr
synthType (S.Ann s _ e) = mapSynth (pushSpan s) $ case e of
  S.TVar n          -> tvar n
  S.KType           -> _Type
  S.KInterface      -> _Interface
  S.TString         -> _String
  S.TForAll n t b   -> forAll (n ::: checkType t) (checkType b)
  S.TArrow  n q a b -> (map checkInterface <$> n ::: ((maybe Many interpretMul q,) <$> checkType a)) --> checkType b
  S.TComp s t       -> comp (map checkInterface s) (checkType t)
  S.TApp f a        -> app TApp (synthType f) (checkType a)
  where
  interpretMul = \case
    S.Zero -> zero
    S.One  -> one

-- | Check a type at a kind.
--
-- NB: while synthesis is possible for all types at present, I reserve the right to change that.
checkType :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> Check m TExpr
checkType = switch . synthType

synthInterface :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Interface -> Synth m TExpr
synthInterface (S.Ann s _ (S.Interface (S.Ann sh _ h) sp)) = mapSynth (pushSpan s) $
  foldl' (app TApp) h' (checkType <$> sp)
  where
  h' = mapSynth (pushSpan sh) (tvar h)

checkInterface :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Interface -> Check m TExpr
checkInterface = switch . synthInterface
