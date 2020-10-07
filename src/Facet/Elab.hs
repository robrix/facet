{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Elab
( Context
, implicit
, elab
, Elab(..)
, Check(..)
, Synth(..)
, check
, switch
, unify
  -- * Types
, elabType
, tglobal
, tbound
, _Type
, _Unit
, (.$)
, (.*)
, (-->)
, (>~>)
  -- * Expressions
, elabExpr
, eglobal
, ebound
, ($$)
, tlam
, lam
, unit
, (**)
  -- * Declarations
, elabDecl
  -- * Modules
, elabModule
) where

import           Control.Algebra
import           Control.Carrier.Reader
import           Control.Effect.Parser.Span (Span(..))
import           Control.Lens (preview, review)
import           Data.Bifunctor (first)
import           Data.Foldable (toList)
import qualified Data.IntMap as IntMap
import qualified Data.Text as T
import           Facet.Carrier.Error.Context
import qualified Facet.Core as C
import qualified Facet.Core.Pattern as CP
import           Facet.Core.Type
import qualified Facet.Env as Env
import           Facet.Name (MName(..), Name(..), QName(..), prettyNameWith)
import qualified Facet.Name as N
import           Facet.Pretty (reflow)
import qualified Facet.Print as P
import           Facet.Stack
import qualified Facet.Surface.Comp as SC
import qualified Facet.Surface.Decl as SD
import qualified Facet.Surface.Expr as SE
import qualified Facet.Surface.Module as SM
import qualified Facet.Surface.Pattern as SP
import qualified Facet.Surface.Type as ST
import           Facet.Syntax
import           Prelude hiding ((**))
import           Silkscreen (colon, fillSep, group, pretty, softline, (<+>), (</>))

type Context = IntMap.IntMap Type

implicit :: Env.Env
implicit = Env.fromList [ (N.T (N.TName (T.pack "Type")), MName (T.pack "Facet") ::: C._Type) ]

elab :: Applicative m => MName -> Span -> Env.Env -> Context -> Elab m a -> m (Either (Span, P.Print) a)
elab n s e c (Elab m) = runError (curry (pure . Left)) (pure . Right) s (m n e c)

newtype Elab m a = Elab (MName -> Env.Env -> Context -> ErrorC Span P.Print m a)
  deriving (Algebra (Reader MName :+: Reader Env.Env :+: Reader Context :+: Error P.Print :+: Reader Span :+: sig), Applicative, Functor, Monad) via ReaderC MName (ReaderC Env.Env (ReaderC Context (ErrorC Span P.Print m)))


newtype Check m a = Check { runCheck :: Type -> Elab m a }
  deriving (Algebra (Reader Type :+: Reader MName :+: Reader Env.Env :+: Reader Context :+: Error P.Print :+: Reader Span :+: sig), Applicative, Functor, Monad) via ReaderC Type (Elab m)

newtype Synth m a = Synth { synth :: Elab m (a ::: Type) }

instance Functor m => Functor (Synth m) where
  fmap f (Synth m) = Synth (first f <$> m)

check :: (Check m a ::: Type) -> Elab m a
check = uncurryAnn runCheck

switch :: Algebra sig m => Synth m a -> Check m a
switch s = Check $ \ _T -> do
  a ::: _T' <- synth s
  a <$ unify _T _T'

unify :: Algebra sig m => Type -> Type -> Elab m ()
unify t1 t2 = go t1 t2
  where
  go t1 t2 = case (out t1, out t2) of
    (Type,      Type)       -> pure ()
    (Unit,      Unit)       -> pure ()
    (l1 :* r1,  l2 :* r2)   -> go l1 l2 *> go r1 r2
    -- FIXME: we try to unify Type-the-global with Type-the-constant
    -- FIXME: resolve globals to try to progress past certain inequalities
    (f1 :$ a1,  f2 :$ a2)
      | f1 == f2
      , Just _ <- goS a1 a2 -> pure ()
    (a1 :-> b1, a2 :-> b2)  -> go a1 a2 *> go b1 b2
    (t1 :=> b1, t2 :=> b2)  -> go (ty t1) (ty t2) *> go b1 b2
    -- FIXME: build and display a diff of the root types
    _                       -> couldNotUnify t1 t2
  goS Nil        Nil        = Just (pure ())
  goS (i1 :> l1) (i2 :> l2) = (*>) <$> goS i1 i2 <*> Just (go l1 l2)
  goS _          _          = Nothing


-- General

bound :: Algebra sig m => Name -> (Name -> e) -> (Int -> P.Print) -> Synth m e
bound n with var = Synth $ asks (IntMap.lookup (id' n)) >>= \case
  Just b  -> pure (with n ::: b)
  Nothing -> freeVariable (prettyNameWith var n)

app :: Algebra sig m => (a -> a -> a) -> Synth m a -> Check m a -> Synth m a
app ($$) f a = Synth $ do
  f' ::: _F <- synth f
  (_A, _B) <- expectFunctionType (pretty "in application") _F
  a' <- check (a ::: _A)
  pure $ f' $$ a' ::: _B


-- Types

elabType :: Algebra sig m => (ST.Type ::: Maybe Type) -> Elab m (Type ::: Type)
elabType (t ::: _K) = ST.fold alg t _K
  where
  alg t _K = case t of
    ST.Free  n -> validate =<< synth (tglobal n)
    ST.Bound n -> validate =<< synth (tbound n)
    ST.Hole  n -> hole (n ::: _K)
    ST.Type    -> validate =<< synth _Type
    ST.Void    -> validate =<< synth _Void
    ST.Unit    -> validate =<< synth _Unit
    t ST.:=> b -> validate =<< synth (fmap _check t >~> _check b)
    f ST.:$  a -> validate =<< synth (_synth f .$  _check a)
    a ST.:-> b -> validate =<< synth (_check a --> _check b)
    l ST.:*  r -> validate =<< synth (_check l .*  _check r)
    ST.Loc s b -> local (const s) $ b _K
    where
    _check r = tm <$> Check (r . Just)
    _synth r = Synth (r Nothing)
    validate r@(_T ::: _K') = case _K of
      Just _K -> r <$ unify _K' _K
      _       -> pure r

tglobal :: (C.Type ty, Algebra sig m) => N.DName -> Synth m ty
tglobal n = Synth $ asks (Env.lookup n) >>= \case
  Just b  -> pure (C.tglobal (tm b :.: n) ::: ty b)
  Nothing -> freeVariable (pretty n)

tbound :: (C.Type ty, Algebra sig m) => Name -> Synth m ty
tbound n = bound n C.tbound P.tvar

_Type :: C.Type t => Synth m t
_Type = Synth $ pure $ C._Type ::: C._Type

_Void :: C.Type t => Synth m t
_Void = Synth $ pure $ C._Void ::: C._Type

_Unit :: C.Type t => Synth m t
_Unit = Synth $ pure $ C._Unit ::: C._Type

(.$) :: (Algebra sig m, C.Type t) => Synth m t -> Check m t -> Synth m t
(.$) = app (C..$)

infixl 9 .$

(.*) :: C.Type t => Check m t -> Check m t -> Synth m t
a .* b = Synth $ do
  a' <- check (a ::: C._Type)
  b' <- check (b ::: C._Type)
  pure $ a' C..* b' ::: C._Type

infixl 7 .*

(-->) :: C.Type t => Check m t -> Check m t -> Synth m t
a --> b = Synth $ do
  a' <- check (a ::: C._Type)
  b' <- check (b ::: C._Type)
  pure $ (a' C.--> b') ::: C._Type

infixr 2 -->

(>~>)
  :: Algebra sig m
  => (Name ::: Check m Type)
  -> Check m Type
  -> Synth m Type
(n ::: t) >~> b = Synth $ do
  _T <- check (t ::: C._Type)
  ftb' <- n ::: _T |- ((n ::: _T) C.>=>) <$> check (b ::: C._Type)
  pure $ ftb' ::: C._Type

infixr 1 >~>


-- Expressions

elabExpr :: (Algebra sig m, C.Expr expr) => (SE.Expr ::: Maybe Type) -> Elab m (expr ::: Type)
elabExpr (t ::: _T) = SE.fold alg t _T
  where
  alg t _T = case t of
    SE.Free  n -> validate =<< synth (eglobal n)
    SE.Bound n -> validate =<< synth (ebound n)
    SE.Hole  n -> hole (n ::: _T)
    f SE.:$  a -> validate =<< synth (_synth f $$  _check a)
    l SE.:*  r -> check (_check l **  _check r ::: _T) (pretty "product")
    SE.Unit    -> validate =<< synth unit
    SE.Comp cs -> check (comp (map (fmap _check) cs) ::: _T) (pretty "computation")
    SE.Loc s b -> local (const s) $ b _T
    where
    _check r = tm <$> Check (r . Just)
    _synth r = Synth (r Nothing)
    check (m ::: _T) msg = expectChecked _T msg >>= \ _T -> (::: _T) <$> runCheck m _T
    validate r@(_ ::: _T') = case _T of
      Just _T -> r <$ unify _T' _T
      _       -> pure r

eglobal :: (Algebra sig m, C.Expr expr) => N.DName -> Synth m expr
eglobal n = Synth $ asks (Env.lookup n) >>= \case
  Just b  -> pure (C.global (tm b :.: n) ::: ty b)
  Nothing -> freeVariable (pretty n)

ebound :: (C.Expr expr, Algebra sig m) => Name -> Synth m expr
ebound n = bound n C.bound P.evar

($$) :: (C.Expr expr, Algebra sig m) => Synth m expr -> Check m expr -> Synth m expr
($$) = app (C.$$)

tlam :: (Algebra sig m, C.Expr expr) => Name -> Check m expr -> Check m expr
tlam n b = Check $ \ ty -> do
  (n', _T, _B) <- expectQuantifiedType (reflow "when checking type lambda") ty
  n' ::: _T |- C.tlam n <$> check (b ::: _B)

lam :: (Algebra sig m, C.Expr expr) => Name -> Check m expr -> Check m expr
lam n b = Check $ \ _T -> do
  (_A, _B) <- expectFunctionType (reflow "when checking lambda") _T
  n ::: _A |- C.lam (review CP.var_ n) <$> check (b ::: _B)

unit :: C.Expr t => Synth m t
unit = Synth . pure $ C.unit ::: C._Unit

(**) :: (C.Expr expr, Algebra sig m) => Check m expr -> Check m expr -> Check m expr
l ** r = Check $ \ _T -> do
  (_L, _R) <- expectProductType (reflow "when checking product") _T
  l' <- check (l ::: _L)
  r' <- check (r ::: _R)
  pure (l' C.** r')

comp :: (Algebra sig m, C.Expr expr) => [SC.Clause (Check m expr)] -> Check m expr
comp cs = do
  cs' <- traverse clause cs
  -- FIXME: extend Core to include pattern matching so this isn’t broken
  -- FIXME: extend Core to include computation types
  pure $ head cs'

clause :: (Algebra sig m, C.Expr expr) => SC.Clause (Check m expr) -> Check m expr
clause = SC.fold $ \case
  SC.Clause p b -> Check $ \ _T -> do
    (_A, _B) <- expectFunctionType (reflow "when checking clause") _T
    p' <- check (pattern p ::: _A)
    foldr (|-) (C.lam (tm <$> p') <$> check (b ::: _B)) p'
  SC.Body e   -> e
  SC.Loc s c  -> local (const s) c


pattern :: Algebra sig m => SP.Pattern N.Name -> Check m (CP.Pattern (N.Name ::: Type))
pattern = SP.fold $ \case
  SP.Wildcard -> pure (review CP.wildcard_ ())
  SP.Var n    -> Check $ \ _T -> pure (review CP.var_ (n ::: _T))
  SP.Tuple ps -> Check $ \ _T -> review CP.tuple_ . toList <$> go _T (fromList ps)
    where
    go _T = \case
      Nil      -> Nil      <$  unify C._Unit _T
      Nil :> p -> (Nil :>) <$> check (p ::: _T)
      ps  :> p -> do
        (_L, _R) <- expectProductType (reflow "when checking tuple pattern") _T
        (:>) <$> go _L ps <*> check (p ::: _R)
  SP.Loc s p  -> local (const s) p


-- Declarations

elabDecl :: (Algebra sig m, C.Expr expr) => SD.Decl -> Elab m (Check m expr ::: Type)
elabDecl = SD.fold alg
  where
  alg = \case
    (n ::: t) SD.:=> b -> do
      _T ::: _  <- elabType (t ::: Just C._Type)
      b' ::: _B <- n ::: _T |- b
      pure $ tlam n b' ::: ((n ::: _T) C.>=> _B)

    (n ::: t) SD.:-> b -> do
      _T ::: _  <- elabType (t ::: Just C._Type)
      b' ::: _B <- n ::: _T |- b
      pure $ lam n b' ::: (_T C.--> _B)

    t SD.:= b -> do
      _T ::: _ <- elabType (t ::: Just C._Type)
      pure $ _check (elabExpr . (b :::)) ::: _T

    SD.Loc s d -> local (const s) d
  _check r = tm <$> Check (r . Just)


-- Modules

elabModule :: (Algebra sig m, C.Module def mod, C.Def expr ty def, C.Type ty, C.Expr expr) => SM.Module -> Elab m mod
elabModule (SM.Module s n ds) = local (const s) $ C.module' n <$> traverse elabDef ds

elabDef :: (Algebra sig m, C.Def expr ty def, C.Type ty, C.Expr expr) => SM.Def -> Elab m def
elabDef (SM.Def s n d) = local (const s) $ do
  e ::: _T <- elabDecl d
  e' <- check (e ::: _T)
  mname <- ask
  -- FIXME: extend the environment
  -- FIXME: extend the module
  -- FIXME: support defining types
  pure $ C.defTerm (mname :.: n) (interpret _T := e')


-- Context

(|-) :: Has (Reader Context) sig m => Name ::: Type -> m a -> m a
n ::: t |- m = local (IntMap.insert (id' n) t) m

infix 1 |-


-- Failures

err :: Has (Error P.Print) sig m => P.Print -> m a
err = throwError . group

hole :: Has (Error P.Print) sig m => (T.Text ::: Maybe Type) -> m (a ::: Type)
hole (n ::: t) = case t of
  Just t  -> err $ fillSep [pretty "found", pretty "hole", pretty n, colon, interpret t]
  Nothing -> couldNotSynthesize (fillSep [ pretty "hole", pretty n ])

mismatch :: Has (Error P.Print) sig m => P.Print -> P.Print -> P.Print -> m a
mismatch msg exp act = err $ msg
  </> pretty "expected:" <+> exp
  </> pretty "  actual:" <+> act

couldNotUnify :: Has (Error P.Print) sig m => Type -> Type -> m a
couldNotUnify t1 t2 = mismatch (reflow "could not unify") (interpret t2) (interpret t1)

couldNotSynthesize :: Has (Error P.Print) sig m => P.Print -> m a
couldNotSynthesize msg = err $ reflow "could not synthesize a type for" <> softline <> msg

freeVariable :: Has (Error P.Print) sig m => P.Print -> m a
freeVariable v = err $ fillSep [reflow "variable not in scope:", v]

expectChecked :: Has (Error P.Print) sig m => Maybe Type -> P.Print -> m Type
expectChecked t msg = maybe (couldNotSynthesize msg) pure t


-- Patterns

expectQuantifiedType :: Has (Error P.Print) sig m => P.Print -> Type -> m (Name, Type, Type)
expectQuantifiedType s _T = case preview forAll_ _T of
  Just ((n ::: _T), _B) -> pure (n, _T, _B)
  _                     -> mismatch s (pretty "{_} -> _") (interpret _T)

expectFunctionType :: Has (Error P.Print) sig m => P.Print -> Type -> m (Type, Type)
expectFunctionType s _T = case preview arrow_ _T of
  Just (_A, _B) -> pure (_A, _B)
  _             -> mismatch s (pretty "_ -> _") (interpret _T)

expectProductType :: Has (Error P.Print) sig m => P.Print -> Type -> m (Type, Type)
expectProductType s _T = case preview prd_ _T of
  Just (_A, _B) -> pure (_A, _B)
  _             -> mismatch s (pretty "(_, _)") (interpret _T)
