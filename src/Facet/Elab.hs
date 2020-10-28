{-# LANGUAGE OverloadedStrings #-}
-- | This module defines the /elaboration/ of terms in 'S.Expr' into values in 'Value'.
--
-- Elaboration is the only way 'Value's are constructed from untrusted terms, and so typechecking is performed at this point. If elaboration succeeds and a 'Value' is returned, that 'Value' does not require further verification; hence, 'Value's elide source span information.
module Facet.Elab
( Type
, Expr
, Elab(..)
, elab
, elabTele
, elabWith
, Check(..)
, Synth(..)
, check
, unify
  -- * General
, global
  -- * Expressions
, elabExpr
, _Type
, tbind
, tcomp
, ($$)
, lam
  -- * Modules
, elabModule
, apply
, applyComp
  -- * Errors
, Err(..)
, Reason(..)
) where

import           Control.Algebra
import           Control.Applicative (liftA2)
import           Control.Carrier.Error.Church
import           Control.Carrier.Reader
import           Control.Carrier.State.Church
import           Control.Effect.Empty
import           Control.Effect.Lens ((.=))
import           Control.Effect.Sum
import           Control.Lens (at, ix)
import           Control.Monad ((<=<))
import           Data.Bifunctor (first)
import           Data.Foldable (foldl', for_, toList)
import qualified Data.IntMap as IntMap
import           Data.Maybe (catMaybes)
import qualified Data.Set as Set
import           Data.Traversable (for, mapAccumL)
import           Facet.Context as Context
import           Facet.Core hiding (global, ($$))
import qualified Facet.Core as Binding (Binding(..))
import qualified Facet.Core as C
import           Facet.Effect.Trace as Trace
import           Facet.Graph as Graph
import           Facet.Name hiding (L, R)
import           Facet.Span (Span(..))
import           Facet.Stack hiding ((!?))
import qualified Facet.Surface as S
import           Facet.Syntax
import           GHC.Stack

newtype Elab a = Elab { runElab :: forall sig m . Has (Reader (Context Type) :+: Reader Graph :+: Reader Module :+: Reader [Interface] :+: Reader Span :+: State Subst :+: Throw Err :+: Trace) sig m => m a }

instance Functor Elab where
  fmap f (Elab m) = Elab (fmap f m)

instance Applicative Elab where
  pure a = Elab $ pure a
  Elab f <*> Elab a = Elab (f <*> a)

instance Monad Elab where
  Elab m >>= f = Elab $ m >>= runElab . f

instance Algebra (Reader (Context Type) :+: Reader Graph :+: Reader Module :+: Reader [Interface] :+: Reader Span :+: State Subst :+: Throw Err :+: Trace) Elab where
  alg hdl sig ctx = case sig of
    L rctx                          -> Elab $ alg (runElab . hdl) (inj rctx)  ctx
    R (L graph)                     -> Elab $ alg (runElab . hdl) (inj graph) ctx
    R (R (L mod))                   -> Elab $ alg (runElab . hdl) (inj mod)   ctx
    R (R (R (L sig)))               -> Elab $ alg (runElab . hdl) (inj sig)   ctx
    R (R (R (R (L span))))          -> Elab $ alg (runElab . hdl) (inj span)  ctx
    R (R (R (R (R (L subst)))))     -> Elab $ alg (runElab . hdl) (inj subst) ctx
    R (R (R (R (R (R (L throw)))))) -> Elab $ alg (runElab . hdl) (inj throw) ctx
    R (R (R (R (R (R (R trace)))))) -> Elab $ alg (runElab . hdl) (inj trace) ctx

elab :: Has (Reader Graph :+: Reader Module :+: Reader Span :+: Throw Err :+: Trace) sig m => Elab Value -> m Value
elab = elabWith (fmap pure . apply)

elabTele :: Has (Reader Graph :+: Reader Module :+: Reader Span :+: Throw Err :+: Trace) sig m => Elab Comp -> m Comp
elabTele = elabWith (fmap pure . applyComp)

elabWith :: Has (Reader Graph :+: Reader Module :+: Reader Span :+: Throw Err :+: Trace) sig m => (Subst -> a -> m b) -> Elab a -> m b
elabWith f = runSubstWith f . runContext . runSig . runElab


-- FIXME: it’d be pretty cool if this produced a witness for the satisfaction of the checked type.
newtype Check a = Check { runCheck :: Maybe Type -> Elab a }
  deriving (Algebra (Reader (Maybe Type) :+: Reader (Context Type) :+: Reader Graph :+: Reader Module :+: Reader [Interface] :+: Reader Span :+: State Subst :+: Throw Err :+: Trace), Applicative, Functor, Monad) via ReaderC (Maybe Type) Elab

newtype Synth a = Synth { synth :: Elab (a ::: Type) }

instance Functor Synth where
  fmap f (Synth m) = Synth (first f <$> m)

check :: (Check a ::: Maybe Type) -> Elab a
check (m ::: _T) = runCheck m _T


checkElab :: Check (a ::: b) -> Check a
checkElab m = tm <$> m

synthElab :: Check (a ::: Type) -> Synth a
synthElab m = Synth (runCheck m Nothing)


unify :: Type :===: Type -> Elab Type
unify = trace "unify" . \case
  -- FIXME: this is missing a lot of cases
  VType                    :===: VType                    -> pure VType
  VInterface               :===: VInterface               -> pure VInterface
  -- FIXME: resolve globals to try to progress past certain inequalities
  VNeut h1 e1              :===: VNeut h2 e2
    | h1 == h2
    , Just e' <- unifySpine (e1 :===: e2)                 -> VNeut h1 <$> e'
  VNeut (Metavar v) Nil    :===: x                        -> solve (v :=: x)
  x                        :===: VNeut (Metavar v) Nil    -> solve (v :=: x)
  VComp t1                 :===: VComp t2                 -> VComp <$> unifyComp (t1 :===: t2)
  VComp (Comp [] t1) :===: t2                       -> unify (t1 :===: t2)
  t1                       :===: VComp (Comp [] t2) -> unify (t1 :===: t2)
  -- FIXME: build and display a diff of the root types
  t1                       :===: t2                       -> couldNotUnify "mismatch" t1 t2
  where
  unifySpine (Nil      :===: Nil)      = Just (pure Nil)
  -- NB: we make no attempt to unify case eliminations because they shouldn’t appear in types anyway.
  unifySpine (i1 :> l1 :===: i2 :> l2)
    | fst l1 == fst l2                 = liftA2 (:>) <$> unifySpine (i1 :===: i2) <*> Just ((fst l1,) <$> unify (snd l1 :===: snd l2))
  unifySpine _                         = Nothing

  solve (n :=: val') = do
    subst <- get
    -- FIXME: occurs check
    case subst IntMap.! getMeta n of
      Just val ::: _T -> unify (val' :===: val)
      Nothing  ::: _T -> val' <$ put (insertSubst n (Just val' ::: _T) subst)

unifyComp :: Comp :===: Comp -> Elab Comp
unifyComp = \case
  ForAll (Binding p1 n1 s1 t1) b1 :===: ForAll (Binding p2 _  s2 t2) b2
    | p1 == p2 -> do
      -- FIXME: unify the signatures
      s <- unifySig (s1 :===: s2)
      t <- unify (t1 :===: t2)
      d <- asks @(Context Type) level
      let v = free d
      b <- unifyComp (b1 v :===: b2 v)
      pure $ ForAll (Binding p1 n1 s t) (\ v -> C.bindComp d v b)
  Comp s1 t1 :===: Comp s2 t2 -> Comp <$> unifySig (s1 :===: s2) <*> unify (t1 :===: t2)
  Comp [] t1 :===: t2         -> fromValue <$> unify (t1 :===: VComp t2)
  t1         :===: Comp [] t2 -> fromValue <$> unify (VComp t1 :===: t2)
  t1         :===: t2         -> couldNotUnify "mismatch" (VComp t1) (VComp t2)
  where
  -- FIXME: unify the signatures
  unifySig (s1 :===: _) = pure s1


-- FIXME: should we give metas names so we can report holes or pattern variables cleanly?
meta :: Type -> Elab Meta
meta _T = do
  subst <- get
  let m = Meta (length subst)
  m <$ put (insertSubst m (Nothing ::: _T) subst)

-- FIXME: does instantiation need to be guided by the expected type?
-- FIXME: can implicits have effects? what do we do about the signature?
-- FIXME: can we avoid metas if we instantiate against a whole spine?
instantiate :: Expr ::: Comp -> Elab (Expr ::: Comp)
instantiate (e ::: _T) = case _T of
  ForAll (Binding Im _ _ _T) _B -> do
    m <- metavar <$> meta _T
    instantiate (e C.$$ (Im, m) ::: _B m)
  _                           -> pure $ e ::: _T


-- General

switch
  :: Synth a
  -> Check (a ::: Type)
switch (Synth m) = Check $ trace "switch" . \case
  Just _K -> m >>= \ (a ::: _K') -> (a :::) <$> unify (_K' :===: _K)
  _       -> m

as :: (Check a ::: Type) -> Synth a
as (m ::: _T) = Synth ((::: _T) <$> check (m ::: Just _T))

resolveWith
  :: (forall sig m . Has Empty sig m => Module -> m (QName :=: Maybe Def ::: Comp))
  -> Maybe MName
  -> DName
  -> Elab (QName :=: Maybe Def ::: Comp)
resolveWith lookup m n = asks lookup >>= \case
  Just (n' :=: d ::: _T) -> pure $ n' :=: d ::: _T
  Nothing                -> do
    defs <- asks (foldMap (lookup . snd) . getGraph)
    case defs of
      []                -> freeVariable m n
      [n' :=: d ::: _T] -> pure $ n' :=: d ::: _T
      -- FIXME: resolve ambiguities by type.
      _                 -> ambiguousName m n (map (\ (q :=: _ ::: _) -> q) defs)

resolve
  :: DName
  -> Elab (QName :=: Maybe Def ::: Comp)
resolve n = resolveWith (lookupD n) Nothing n

resolveC
  :: UName
  -> Elab (QName :=: Maybe Def ::: Comp)
resolveC n = resolveWith (lookupC n) Nothing (C n)

resolveQ
  :: QName
  -> Elab (QName :=: Maybe Def ::: Comp)
resolveQ q@(m :.: n) = lookupQ q <$> ask <*> ask >>= \case
  Just (q' :=: d ::: _T) -> pure $ q' :=: d ::: _T
  Nothing                -> freeVariable (Just m) n

resolveMD :: Maybe MName -> DName -> Elab (QName :=: Maybe Def ::: Comp)
resolveMD m n = maybe (resolve n) (resolveQ . (:.: n)) m

-- FIXME: we’re instantiating when inspecting types in the REPL.
global
  :: QName ::: Comp
  -> Synth Value
global (q ::: _T) = Synth $ fmap VComp <$> instantiate (C.global q ::: _T)

lookupInContext :: DName -> Context Type -> Maybe (Level, Type)
lookupInContext n ctx = maybe Nothing (`lookupLevel` ctx) (eOrT n)
  where
  eOrT (E n) = Just n
  eOrT (T n) = Just n
  eOrT _     = Nothing

lookupInSig :: UName -> [Interface] -> Maybe (UName ::: Comp)
lookupInSig n = matchWith $ matchWith (\ t -> t <$ guard (tm t == n)) . ops

-- FIXME: do we need to instantiate here to deal with rank-n applications?
var
  :: Maybe MName
  -> DName
  -> Synth Value
var m n = Synth $ ask >>= \ ctx -> case m of
  Nothing
    | Just (i, _T) <- lookupInContext n ctx
    -> pure (free i ::: _T)
  _ -> do
    n :=: _ ::: _T <- resolveMD m n
    synth $ global (n ::: _T)

hole
  :: UName
  -> Check a
hole n = Check $ expectChecked "hole" $ \ _T -> err $ Hole n _T

($$)
  :: Synth Value
  -> Check Value
  -> Synth Value
f $$ a = Synth $ do
  f' ::: _F <- synth f
  -- FIXME: check that the signatures match
  (_A, _B) <- expectQuantifier "in application" _F
  a' <- check (a ::: Just (Binding.type' _A))
  pure $ f' C.$$ (Ex, a') ::: VComp (_B a')


elabBinder
  :: Has (Reader (Context Type)) sig m
  => (Value -> m Value)
  -> m (Value -> Value)
elabBinder b = do
  d <- asks @(Context Type) level
  b' <- b (free d)
  pure $ \ v -> C.bind d v b'

elabBinders
  :: (Traversable t, Has (Reader (Context Type)) sig m)
  => t (UName ::: Type)
  -> (t (UName ::: Type) -> m Value)
  -> m (t Type -> Value)
elabBinders p b = do
  d <- asks @(Context Type) level
  b' <- b p
  pure $ \ v -> C.binds (snd (foldl' (\ (d, s) v -> (succ d, IntMap.insert (getLevel d) v s)) (d, IntMap.empty) v)) b'

(|-)
  :: Has (Reader (Context Type)) sig m
  => UName ::: Type
  -> m a
  -> m a
t |- b = local @(Context Type) (|> t) b

infix 1 |-


-- Expressions

elabExpr
  :: HasCallStack
  => S.Ann S.Expr
  -> Check (Expr ::: Type)
elabExpr = withSpan $ \case
  S.Var m n    -> switch $ var m n
  S.Hole  n    -> hole n
  S.Type       -> trace "Type" $ switch _Type
  S.TInterface -> trace "Interface" $ switch _Interface
  S.TComp t    -> trace "forall" $ switch $ VComp <$> elabSTelescope t
  S.App f a    -> switch $ synthElab (elabExpr f) $$ checkElab (elabExpr a)
  S.Lam cs     -> elabClauses cs
  S.Thunk e    -> elabExpr e -- FIXME: this should convert between value and computation type
  S.Force e    -> elabExpr e -- FIXME: this should convert between computation and value type

elabBinding :: S.Ann S.Binding -> [Check Binding]
elabBinding (S.Ann s _ (S.Binding p n d t)) = [ Binding p n <$> setSpan s (traverse elabSig d) <*> checkElab (elabExpr t) | n <- toList n ]

-- FIXME: synthesize the types of the operands against the type of the interface; this is a spine.
elabSig :: S.Ann S.Interface -> Check Interface
elabSig = withSpan $ \ (S.Interface q t) -> do
  q :=: d ::: _T <- withSpan (Check . const . uncurry resolveMD) q
  sp <- traverse (checkElab . elabExpr) t
  let ops = case d of
        Just (DInterface ops) -> ops
        _                     -> []
  pure $ Interface q sp ops

elabSTelescope :: S.Ann S.Comp -> Synth Comp
elabSTelescope (S.Ann s _ (S.Comp bs d t)) = Synth $ setSpan s $ synth $ foldr (\ t b -> tbind t (\ v -> v |- checkElab (switch b))) (as (Comp <$> traverse elabSig d <*> checkElab (elabExpr t) ::: VType)) (elabBinding =<< bs)


_Type :: Synth Type
_Type = Synth $ pure $ VType ::: VType

_Interface :: Synth Type
_Interface = Synth $ pure $ VInterface ::: VType


tbind :: Check Binding -> (UName ::: Type -> Check Comp) -> Synth Comp
tbind t b = Synth $ trace "telescope" $ do
  -- FIXME: should we check that the signature is empty?
  _T@Binding{ name, type' = _A } <- check (t ::: Just VType)
  d <- asks @(Context Type) level
  _B <- check (b (name ::: _A) ::: Just VType)
  pure $ ForAll _T (\ v -> C.bindComp d v _B) ::: VType

tcomp :: Elab [Interface] -> Check Type -> Synth Comp
tcomp s t = Synth $ do
  s' <- s
  t' <- check (t ::: Just VType)
  pure $ Comp s' t' ::: VType


lam
  :: (Pl, UName)
  -> (UName ::: Type -> Check Expr)
  -> Check Expr
lam n b = Check $ expectChecked "lambda" $ \ _T -> do
  -- FIXME: how does the effect adjustment change this?
  (Binding _ _ _ _T, _B) <- expectQuantifier "when checking lambda" _T
  b' <- elabBinder $ \ v -> check (b (snd n ::: _T) ::: Just (VComp (_B v)))
  pure $ VLam (fst n) [Clause (PVar (snd n ::: _T)) (b' . unsafeUnPVar)]


-- FIXME: go find the pattern matching matrix algorithm
elabClauses :: [S.Clause] -> Check (Expr ::: Type)
elabClauses [S.Clause (S.Ann _ _ (S.PVar n)) b] = Check $ expectChecked "variable pattern" $ \ _T -> do
  -- FIXME: error if the signature is non-empty; variable patterns don’t catch effects.
  (Binding pl _ _ _A, _B) <- expectQuantifier "when checking clauses" _T
  b' <- elabBinder $ \ v -> n ::: _A |- check (checkElab (elabExpr b) ::: Just (VComp (_B v)))
  pure $ VLam pl [Clause (PVar (n ::: _A)) (b' . unsafeUnPVar)] ::: _T
-- FIXME: this is incorrect in the presence of wildcards (or something). e.g. { (true) (true) -> true, _ _ -> false } gets the inner {(true) -> true} clause from the first case appended to the
elabClauses cs = Check $ expectChecked "clauses" $ \ _T -> do
  -- FIXME: use the signature to elaborate the pattern
  (Binding _ _ _ _A, _B) <- expectQuantifier "when checking clauses" _T
  d <- asks (level @Type)
  let _B' = _B (free d)
  cs' <- for cs $ \ (S.Clause p b) -> check
    (   elabPattern p (\ p' -> do
      Clause p' <$> elabBinders p' (foldr (|-) (check (checkElab (elabExpr b) ::: Just (VComp _B')))))
    ::: Just _A)
  pure $ VLam Ex cs' ::: _T


-- FIXME: check for unique variable names
elabPattern :: S.Ann S.Pattern -> (C.Pattern (UName ::: Type) -> Elab a) -> Check a
elabPattern (S.Ann s _ p) k = Check $ expectChecked "pattern" $ \ _A -> setSpan s $ case p of
  S.PVar n    -> k (C.PVar (n ::: _A))
  S.PCon n ps -> do
    q :=: _ ::: _T' <- resolveC n
    _T'' <- inst _T'
    subpatterns _A _T'' ps $ \ ps' -> k (C.PCon (Con q (fromList ps')))
  -- FIXME: look up the effect in the signature
  S.PEff n ps v -> do
    q :=: _ ::: _T' <- resolveC n
    _T'' <- inst _T'
    -- FIXME: what should the type of the continuation be? [effect result type] -> [remainder of body type after this pattern]?
    subpatterns _A _T'' ps $ \ ps' -> k (C.PEff q (fromList ps') (v ::: VType)) -- FIXME: lies
  where
  inst = \case
  -- FIXME: assert that the signature is empty
    ForAll (Binding Im _ _ _T) _B -> meta _T >>= inst . _B . metavar
    _T                            -> pure _T
  subpatterns _A = go
    where
    go _T' = \case
      []   -> \ k -> unify (VComp _T' :===: _A) *> k []
      p:ps -> \ k -> do
        -- FIXME: assert that the signature is empty
        (Binding _ _ _ _A, _B) <- expectQuantifier "when checking constructor pattern" (VComp _T')
        -- FIXME: is this right? should we use `free` instead? if so, what do we push onto the context?
        v <- metavar <$> meta _A
        check
          (   elabPattern p (\ p' -> go (_B v) ps (\ ps' -> k (p' : ps')))
          ::: Just _A)


-- Declarations

elabDataDef
  :: (Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (Throw Err) sig m, Has Trace sig m)
  => QName ::: Comp
  -> [S.Ann (UName ::: S.Ann S.Comp)]
  -> m [(DName, Decl)]
-- FIXME: check that all constructors return the datatype.
elabDataDef (mname :.: dname ::: _T) constructors = do
  cs <- for constructors $ runWithSpan $ \ (n ::: t) -> do
    c_T <- elabTele $ go (checkElab (switch (elabSTelescope t))) _T
    pure $ n :=: con (mname :.: C n) Nil c_T ::: c_T
  pure
    $ (dname, Decl (Just (C.DData cs)) _T)
    : map (\ (n :=: c ::: c_T) -> (E n, Decl (Just (C.DTerm c)) c_T)) cs
  where
  go k = \case
    Comp _ _                     -> check (k ::: Just VType)
    -- FIXME: can sigs appear here?
    ForAll (Binding _ n s _T) _B -> do
      d <- asks @(Context Type) level
      _B' <- n ::: _T |- go k (_B (free d))
      pure $ ForAll (Binding Im n s _T) (\ v -> C.bindComp d v _B')
  con q fs = \case
    ForAll (Binding p n _ _T) _B -> VLam p [Clause (PVar (n ::: _T)) ((\ v -> con q (fs :> v) (_B v)) . unsafeUnPVar)]
    _T                           -> VCon (Con q fs)

elabInterfaceDef
  :: (Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (Throw Err) sig m, Has Trace sig m)
  => Comp
  -> [S.Ann (UName ::: S.Ann S.Comp)]
  -> m Decl
elabInterfaceDef _T constructors = do
  cs <- for constructors $ runWithSpan $ \ (n ::: t) ->
    (n :::) <$> elabTele (go (checkElab (switch (elabSTelescope t))) _T)
  pure $ Decl (Just (DInterface cs)) _T
  where
  go k = \case
    -- FIXME: check that the interface is a member of the sig.
    Comp _ _                     -> check (k ::: Just VType)
    ForAll (Binding _ n s _T) _B -> do
      d <- asks @(Context Type) level
      _B' <- n ::: _T |- go k (_B (free d))
      pure $ ForAll (Binding Im n s _T) (\ v -> C.bindComp d v _B')

-- FIXME: add a parameter for the effect signature.
elabTermDef
  :: (HasCallStack, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (Throw Err) sig m, Has Trace sig m)
  => Comp
  -> S.Ann S.Expr
  -> m Expr
elabTermDef _T expr = runReader (S.ann expr) $ elab $ go (checkElab (elabExpr expr)) _T
  where
  go k t = case t of
    Comp s _T                    -> local (s ++) $ check (k ::: Just _T)
    ForAll (Binding p n _ _T) _B -> do
      b' <- elabBinder $ \ v -> n ::: _T |- go k (_B v)
      pure $ VLam p [Clause (PVar (n ::: _T)) (b' . unsafeUnPVar)]


-- Modules

elabModule
  :: (HasCallStack, Has (Reader Graph) sig m, Has (Throw Err) sig m, Has Trace sig m)
  => S.Ann S.Module
  -> m C.Module
elabModule (S.Ann s _ (S.Module mname is os ds)) = execState (Module mname [] os mempty) . runReader s $ tracePretty mname $ do
  let (importedNames, imports) = mapAccumL (\ names (S.Ann _ _ S.Import{ name }) -> (Set.insert name names, Import name)) Set.empty is
  imports_ .= imports

  local (`restrict` importedNames) $ do
    -- FIXME: maybe figure out the graph for mutual recursion?
    -- FIXME: check for redundant naming

    -- elaborate all the types first
    es <- trace "types" $ for ds $ \ (S.Ann _ _ (dname, S.Ann s _ (S.Decl tele def))) -> tracePretty dname $ setSpan s $ do
      _T <- runModule . elabTele $ check (checkElab (switch (elabSTelescope tele)) ::: Just VType)

      decls_.at dname .= Just (Decl Nothing _T)
      case def of
        S.DataDef cs -> do
          decls <- runModule $ elabDataDef (mname :.: dname ::: _T) cs
          Nothing <$ for_ decls (\ (dname, decl) -> decls_.at dname .= Just decl)

        S.InterfaceDef os -> do
          decl <- runModule $ elabInterfaceDef _T os
          Nothing <$ (decls_.at dname .= Just decl)

        S.TermDef t -> pure (Just (S.ann tele, dname, t ::: _T))

    -- then elaborate the terms
    trace "definitions" $ for_ (catMaybes es) $ \ (s, dname, t ::: _T) -> setSpan s $ tracePretty dname $ do
      t' <- runModule $ elabTermDef _T t
      decls_.ix dname .= Decl (Just (C.DTerm t')) _T


runSubstWith :: (Subst -> a -> m b) -> StateC Subst m a -> m b
runSubstWith with = runState with emptySubst

runContext :: ReaderC (Context Type) m a -> m a
runContext = runReader Context.empty

-- FIXME: this should carry the operations and their types.
runSig :: ReaderC [Interface] m a -> m a
runSig = runReader []

runModule :: Has (State Module) sig m => ReaderC Module m a -> m a
runModule m = do
  mod <- get
  runReader mod m


-- Errors

setSpan :: Has (Reader Span) sig m => Span -> m a -> m a
setSpan = local . const

withSpan :: Has (Reader Span) sig m => (a -> m b) -> S.Ann a -> m b
withSpan k (S.Ann s _ a) = setSpan s (k a)

runWithSpan :: (a -> ReaderC Span m b) -> S.Ann a -> m b
runWithSpan k (S.Ann s _ a) = runReader s (k a)


data Err = Err
  { span      :: Span
  , reason    :: Reason
  , context   :: Context Type
  , callStack :: Stack Message -- FIXME: keep source references for each message.
  }

data Reason
  = FreeVariable (Maybe MName) DName
  -- FIXME: add source references for the imports, definition sites, and any re-exports.
  | AmbiguousName (Maybe MName) DName [QName]
  | CouldNotSynthesize String
  | Mismatch String (Either String Type) Type
  | Hole UName Type


-- FIXME: apply the substitution before showing this to the user
err :: Reason -> Elab a
err reason = do
  span <- ask
  ctx <- ask
  callStack <- Trace.callStack
  throwError $ Err span reason ctx callStack

mismatch :: String -> Either String Type -> Type -> Elab a
mismatch msg exp act = err $ Mismatch msg exp act

couldNotUnify :: String -> Type -> Type -> Elab a
couldNotUnify msg t1 t2 = mismatch msg (Right t2) t1

couldNotSynthesize :: String -> Elab a
couldNotSynthesize = err . CouldNotSynthesize

freeVariable :: Maybe MName -> DName -> Elab a
freeVariable m n = err $ FreeVariable m n

ambiguousName :: Maybe MName -> DName -> [QName] -> Elab a
ambiguousName n d qs = err $ AmbiguousName n d qs

expectChecked :: String -> (Type -> Elab a) -> Maybe Type -> Elab a
expectChecked msg = maybe (couldNotSynthesize msg)


-- Patterns

expectMatch :: (Type -> Maybe out) -> String -> String -> Type -> Elab out
expectMatch pat exp s _T = maybe (mismatch s (Left exp) _T) pure (pat _T)

expectQuantifier :: String -> Type -> Elab (Binding, Type -> Comp)
expectQuantifier = expectMatch (\case{ ForAll t b -> pure (t, b) ; _ -> Nothing } <=< stripEmpty) "{_} -> _"

stripEmpty :: Type -> Maybe Comp
stripEmpty = \case
  VComp (Comp [] t) -> stripEmpty t
  VComp t           -> Just t
  _                 -> Nothing
