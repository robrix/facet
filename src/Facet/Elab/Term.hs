{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
module Facet.Elab.Term
( -- * General combinators
  switch
, as
  -- * Term combinators
, global
, var
, tlam
, lam
, app
, string
, let'
, comp
  -- * Pattern combinators
, wildcardP
, varP
, conP
, fieldsP
, allP
  -- * Expression elaboration
, synthExpr
, checkExpr
, bindPattern
  -- * Declarations
, elabDataDef
, elabInterfaceDef
, elabTermDef
  -- * Modules
, elabModule
  -- * Elaboration
, require
  -- * Judgements
, check
, Check(..)
, mapCheck
, Synth(..)
, mapSynth
, bind
, Bind(..)
, mapBind
) where

import           Control.Algebra
import           Control.Carrier.Reader
import           Control.Carrier.State.Church
import           Control.Effect.Lens (view, views, (.=))
import           Control.Effect.Throw
import           Control.Effect.Writer (censor)
import           Control.Lens (at, ix)
import           Data.Bifunctor (first)
import           Data.Either (partitionEithers)
import           Data.Foldable
import           Data.Functor
import           Data.Maybe (catMaybes, fromMaybe, listToMaybe)
import           Data.Monoid (Ap(..), First(..))
import qualified Data.Set as Set
import           Data.Text (Text)
import           Data.Traversable (for, mapAccumL)
import           Facet.Context (toEnv)
import           Facet.Effect.Write
import           Facet.Elab
import           Facet.Elab.Type
import           Facet.Graph
import           Facet.Interface
import           Facet.Kind
import           Facet.Lens (locally)
import           Facet.Module as Module
import           Facet.Name
import           Facet.Pattern
import           Facet.Semiring (Few(..), zero, (><<))
import           Facet.Snoc
import           Facet.Snoc.NonEmpty as NE
import           Facet.Source (Source)
import           Facet.Subst
import qualified Facet.Surface as S
import           Facet.Syntax
import           Facet.Term as E
import qualified Facet.Type.Expr as TX
import           Facet.Type.Norm as T hiding (global)
import           Facet.Unify
import           Facet.Usage hiding (restrict)
import           GHC.Stack

-- General combinators

switch :: (HasCallStack, Has (Throw Err) sig m) => Synth m a -> Check m a
switch (Synth m) = Check $ \ _Exp -> m >>= \case
  a ::: T.Comp req _Act -> require req >> unify (Exp _Exp) (Act _Act) $> a
  a :::            _Act -> unify (Exp _Exp) (Act _Act) $> a

as :: (HasCallStack, Has (Throw Err) sig m) => Check m Expr ::: IsType m Type -> Synth m Expr
as (m ::: _T) = Synth $ do
  _T' <- checkIsType (_T ::: KType)
  a <- check (m ::: _T')
  pure $ a ::: _T'


-- Term combinators

-- FIXME: we’re instantiating when inspecting types in the REPL.
global :: Algebra sig m => RName ::: Type -> Synth m Expr
global (q ::: _T) = Synth $ instantiate const (XVar (Global q) ::: _T)

-- FIXME: do we need to instantiate here to deal with rank-n applications?
-- FIXME: effect ops not in the sig are reported as not in scope
-- FIXME: effect ops in the sig are available whether or not they’re in scope
var :: (HasCallStack, Has (Throw Err) sig m) => QName -> Synth m Expr
var n = Synth $ views context_ (lookupInContext n) >>= \case
  [(n', q, CT _T)] -> use n' q $> (XVar (Free n') ::: _T)
  _                -> resolveQ n >>= \case
    n :=: DTerm _ _T -> synth $ global (n ::: _T)
    _ :=: _          -> freeVariable n


hole :: (HasCallStack, Has (Throw Err) sig m) => Name -> Check m a
hole n = Check $ \ _T -> withFrozenCallStack $ err $ Hole n (CT _T)


tlam :: (HasCallStack, Has (Throw Err) sig m) => Check m Expr -> Check m Expr
tlam b = Check $ \ _T -> do
  (n ::: _A, _B) <- assertQuantifier _T
  d <- depth
  (zero, PVar (n ::: CK _A)) |- check (b ::: _B (T.free (LName d n)))

lam :: (HasCallStack, Has (Throw Err) sig m) => [(Bind m (Pattern (Name ::: Classifier)), Check m Expr)] -> Check m Expr
lam cs = Check $ \ _T -> do
  (_A, _B) <- assertTacitFunction _T
  XLam <$> traverse (\ (p, b) -> bind (p ::: _A) (check (b ::: _B))) cs

lam1 :: (HasCallStack, Has (Throw Err) sig m) => Bind m (Pattern (Name ::: Classifier)) -> Check m Expr -> Check m Expr
lam1 p b = lam [(p, b)]

app :: (HasCallStack, Has (Throw Err) sig m) => (a -> b -> c) -> (HasCallStack => Synth m a) -> (HasCallStack => Check m b) -> Synth m c
app mk operator operand = Synth $ do
  f' ::: _F <- synth operator
  (_ ::: (q, _A), _B) <- assertFunction _F
  a' <- censor @Usage (q ><<) $ check (operand ::: _A)
  pure $ mk f' a' ::: _B


string :: Text -> Synth m Expr
string s = Synth $ pure $ XString s ::: T.String


let' :: (HasCallStack, Has (Throw Err) sig m) => Bind m (Pattern (Name ::: Classifier)) -> Synth m Expr -> Check m Expr -> Check m Expr
let' p a b = Check $ \ _B -> do
  a' ::: _A <- synth a
  (p', b') <- bind (p ::: (Many, _A)) (check (b ::: _B))
  pure $ XLet p' a' b'


comp :: Has (Throw Err) sig m => Check m Expr -> Check m Expr
comp b = Check $ \ _T -> do
  (sig, _B) <- assertComp _T
  StaticContext{ graph, module' } <- ask
  let interfacePattern :: Has (Throw Err) sig m => Interface Type -> Elab m (RName :=: (Name ::: Classifier))
      interfacePattern (Interface n _) = maybe (freeVariable (toQ n)) (\ (n' :=: _T) -> pure ((n .:. n') :=: (n' ::: CT _T))) (listToMaybe (scopeToList . tm =<< unDInterface . def =<< lookupQ graph module' (toQ n)))
  p' <- traverse interfacePattern (interfaces sig)
  -- FIXME: can we apply quantities to dictionaries? what would they mean?
  b' <- (Many, PDict p') |- check (b ::: _B)
  pure $ XComp (map (fmap tm) p') b'


-- Pattern combinators

wildcardP :: Bind m (Pattern (Name ::: Classifier))
wildcardP = Bind $ \ _T k -> k PWildcard

varP :: Name -> Bind m (Pattern (Name ::: Classifier))
varP n = Bind $ \ _A k -> k (PVar (n ::: CT (wrap _A)))
  where
  wrap = \case
    T.Comp sig _A -> T.Arrow Nothing Many (T.Ne (Global (NE.FromList ["Data", "Unit"] :.: U "Unit")) Nil) (T.Comp sig _A)
    _T            -> _T

conP :: (HasCallStack, Has (Throw Err) sig m) => QName -> [Bind m (Pattern (Name ::: Classifier))] -> Bind m (Pattern (Name ::: Classifier))
conP n fs = Bind $ \ _A k -> do
  n' :=: _ ::: _T <- resolveC n
  _T' <- maybe (pure _T) (foldl' (\ _T _A -> ($ _A) . snd <$> (_T >>= assertQuantifier)) (pure _T) . snd) (unNeutral _A)
  fs' <- runBind (fieldsP fs) _T' (\ (fs, _T) -> fs <$ unify (Exp _A) (Act _T))
  k $ PCon n' (fromList fs')

fieldsP :: (HasCallStack, Has (Throw Err) sig m) => [Bind m a] -> Bind m ([a], Type)
fieldsP = foldr cons nil
  where
  cons p ps = Bind $ \ _A k -> do
    (_ ::: (_, _A'), _A'') <- assertFunction _A
    runBind p _A' $ \ p' -> runBind ps _A'' (k . first (p' :))
  nil = Bind $ \ _T k -> k ([], _T)


allP :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => Name -> Bind m (Pattern (Name ::: Classifier))
allP n = Bind $ \ _A k -> do
  (sig, _T) <- assertComp _A
  k (PVar (n ::: CT (T.Arrow Nothing Many (T.Ne (Global (NE.FromList ["Data", "Unit"] :.: U "Unit")) Nil) (T.Comp sig _T))))


-- Expression elaboration

synthExpr :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Expr -> Synth m Expr
synthExpr = let ?callStack = popCallStack GHC.Stack.callStack in withSpanS $ \case
  S.Var n    -> var n
  S.App f a  -> synthApp f a
  S.As t _T  -> synthAs t _T
  S.String s -> string s
  S.Hole{}   -> nope
  S.Lam{}    -> nope
  where
  nope = Synth couldNotSynthesize
  synthApp :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Expr -> S.Ann S.Expr -> Synth m Expr
  synthApp f a = app XApp (synthExpr f) (checkExpr a)
  synthAs :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Expr -> S.Ann S.Type -> Synth m Expr
  synthAs t _T = as (checkExpr t ::: mapIsType (>>= (\ (_T ::: _K) -> (::: _K) <$> evalTExpr _T)) (synthType _T))


checkExpr :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Expr -> Check m Expr
checkExpr expr = let ?callStack = popCallStack GHC.Stack.callStack in flip withSpanC expr $ \case
  S.Hole  n  -> hole n
  S.Lam cs   -> checkLam cs
  S.Var{}    -> switch (synthExpr expr)
  S.App{}    -> switch (synthExpr expr)
  S.As{}     -> switch (synthExpr expr)
  S.String{} -> switch (synthExpr expr)

checkLam :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => [S.Clause] -> Check m Expr
checkLam cs = lam (snd vs)
  where
  vs :: Has (Throw Err :+: Write Warn) sig m => ([QName :=: Check m Expr], [(Bind m (Pattern (Name ::: Classifier)), Check m Expr)])
  vs = partitionEithers (map (\ (S.Clause (S.Ann _ _ p) b) -> case p of
    S.PVal p                          -> Right (bindPattern p, checkExpr b)
    S.PEff (S.Ann s _ (S.POp n fs k)) -> Left $ n :=: mapCheck (pushSpan s) (foldr (lam1 . bindPattern) (checkExpr b) (fromList fs:>k))) cs)


-- FIXME: check for unique variable names
bindPattern :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.ValPattern -> Bind m (Pattern (Name ::: Classifier))
bindPattern = go where
  go = withSpanB $ \case
    S.PWildcard -> wildcardP
    S.PVar n    -> varP n
    S.PCon n ps -> conP n (map go ps)


-- | Elaborate a type abstracted over another type’s parameters.
--
-- This is used to elaborate data constructors & effect operations, which receive the type/interface parameters as implicit parameters ahead of their own explicit ones.
abstractType :: (HasCallStack, Has (Throw Err) sig m) => Elab m TX.Type -> Kind -> Elab m TX.Type
abstractType body = go
  where
  go = \case
    KArrow  (Just n) a b -> TX.ForAll n a <$> ((zero, PVar (n ::: CK a)) |- go b)
    _                    -> body

abstractTerm :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => (Snoc TX.Type -> Snoc Expr -> Expr) -> Check m Expr
abstractTerm body = go Nil Nil
  where
  go ts fs = Check $ \case
    T.ForAll n   _T _B -> do
      d <- depth
      check (tlam (go (ts :> LName d n) fs) ::: T.ForAll n _T _B)
    T.Arrow  n q _A _B -> do
      d <- depth
      check (lam [(patternForArgType _A (fromMaybe __ n), go ts (fs :> \ d' -> XVar (Free (LName (levelToIndex d' d) (fromMaybe __ n)))))] ::: T.Arrow n q _A _B)
    _T                -> do
      d <- depth
      pure $ body (TX.Var . Free . Right . fmap (levelToIndex d) <$> ts) (fs <*> pure d)

patternForArgType :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => Type -> Name -> Bind m (Pattern (Name ::: Classifier))
patternForArgType = \case
  T.Comp{} -> allP
  _        -> varP


-- Declarations

elabDataDef
  :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source :+: Throw Err :+: Write Warn) sig m)
  => Name ::: Kind
  -> [S.Ann (Name ::: S.Ann S.Type)]
  -> m [Name :=: Def]
-- FIXME: check that all constructors return the datatype.
elabDataDef (dname ::: _K) constructors = do
  mname <- view name_
  cs <- for constructors $ \ (S.Ann _ _ (n ::: t)) -> do
    c_T <- elabType $ abstractType (checkIsType (synthType t ::: KType)) _K
    con' <- elabTerm $ check (abstractTerm (const (XCon (mname :.: n) . toList)) ::: c_T)
    pure $ n :=: DTerm (Just con') c_T
  pure
    $ (dname :=: DData (scopeFromList cs) _K)
    : cs

elabInterfaceDef
  :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source :+: Throw Err :+: Write Warn) sig m)
  => Name ::: Kind
  -> [S.Ann (Name ::: S.Ann S.Type)]
  -> m [Name :=: Def]
elabInterfaceDef (dname ::: _T) constructors = do
  cs <- for constructors $ \ (S.Ann _ _ (n ::: t)) -> do
    _T' <- elabType $ abstractType (checkIsType (synthType t ::: KType)) _T
    pure $ n :=: _T'
  pure [ dname :=: DInterface (scopeFromList cs) _T ]

-- FIXME: add a parameter for the effect signature.
elabTermDef
  :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source :+: Throw Err :+: Write Warn) sig m)
  => Type
  -> S.Ann S.Expr
  -> m Expr
elabTermDef _T expr@(S.Ann s _ _) = do
  elabTerm $ pushSpan s $ check (go (checkExpr expr) ::: _T)
  where
  go k = Check $ \ _T -> case _T of
    T.ForAll{}               -> check (tlam (go k) ::: _T)
    T.Arrow (Just n) q _A _B -> check (lam [(varP n, go k)] ::: T.Arrow Nothing q _A _B)
    -- FIXME: this doesn’t do what we want for tacit definitions, i.e. where _T is itself a telescope.
    -- FIXME: eta-expanding here doesn’t help either because it doesn’t change the way elaboration of the surface term occurs.
    -- we’ve exhausted the named parameters; the rest is up to the body.
    _                        -> check (k ::: _T)


-- Modules

elabModule
  :: (HasCallStack, Has (Reader Graph :+: Reader Source :+: Throw Err :+: Write Warn) sig m)
  => S.Ann S.Module
  -> m Module
elabModule (S.Ann _ _ (S.Module mname is os ds)) = execState (Module mname [] os mempty) $ do
  let (importedNames, imports) = mapAccumL (\ names (S.Ann _ _ S.Import{ name }) -> (Set.insert name names, Import name)) Set.empty is
  imports_ .= imports

  local (`restrict` importedNames) $ do
    -- FIXME: maybe figure out the graph for mutual recursion?
    -- FIXME: check for redundant naming

    -- elaborate all the types first
    es <- for ds $ \ (S.Ann _ _ (dname, S.Ann _ _ def)) -> case def of
      S.DataDef cs tele -> Nothing <$ do
        _K <- runModule $ elabKind $ checkIsType (synthKind tele ::: KType)
        scope_.decls_.at dname .= Just (DData mempty _K)
        decls <- runModule $ elabDataDef (dname ::: _K) cs
        for_ decls $ \ (dname :=: decl) -> scope_.decls_.at dname .= Just decl

      S.InterfaceDef os tele -> Nothing <$ do
        _K <- runModule $ elabKind $ checkIsType (synthKind tele ::: KType)
        scope_.decls_.at dname .= Just (DInterface mempty _K)
        decls <- runModule $ elabInterfaceDef (dname ::: _K) os
        for_ decls $ \ (dname :=: decl) -> scope_.decls_.at dname .= Just decl

      S.TermDef t tele -> do
        _T <- runModule $ elabType $ checkIsType (synthType tele ::: KType)
        scope_.decls_.at dname .= Just (DTerm Nothing _T)
        pure (Just (dname, t ::: _T))

    -- then elaborate the terms
    for_ (catMaybes es) $ \ (dname, t ::: _T) -> do
      t' <- runModule $ elabTermDef _T t
      scope_.decls_.ix dname .= DTerm (Just t') _T


-- Errors

assertQuantifier :: (HasCallStack, Has (Throw Err) sig m) => Type -> Elab m (Name ::: Kind, Type -> Type)
assertQuantifier = assertMatch (\case{ T.ForAll n t b -> pure (n ::: t, b) ; _ -> Nothing }) "{_} -> _"

-- | Expect a tacit (non-variable-binding) function type.
assertTacitFunction :: (HasCallStack, Has (Throw Err) sig m) => Type -> Elab m ((Quantity, Type), Type)
assertTacitFunction = assertMatch (\case{ T.Arrow Nothing q t b -> pure ((q, t), b) ; _ -> Nothing }) "_ -> _"

-- | Expect a computation type with effects.
assertComp :: (HasCallStack, Has (Throw Err) sig m) => Type -> Elab m (Signature Type, Type)
assertComp = assertMatch unComp "[_] _"


-- Elaboration

runModule :: Has (State Module) sig m => ReaderC Module m a -> m a
runModule m = do
  mod <- get
  runReader mod m

withSpanB :: Algebra sig m => (a -> Bind m b) -> S.Ann a -> Bind m b
withSpanB k (S.Ann s _ a) = mapBind (pushSpan s) (k a)

withSpanC :: Algebra sig m => (a -> Check m b) -> S.Ann a -> Check m b
withSpanC k (S.Ann s _ a) = mapCheck (pushSpan s) (k a)

withSpanS :: Algebra sig m => (a -> Synth m b) -> S.Ann a -> Synth m b
withSpanS k (S.Ann s _ a) = mapSynth (pushSpan s) (k a)

provide :: Has (Reader ElabContext :+: State (Subst Type)) sig m => Signature Type -> m a -> m a
provide sig m = do
  subst <- get
  env <- views context_ toEnv
  locally sig_ (mapSignature (apply subst env) sig :) m

require :: (HasCallStack, Has (Throw Err) sig m) => Signature Type -> Elab m ()
require req = do
  prv <- view sig_
  for_ (interfaces req) $ \ i -> findMaybeM (findMaybeM (runUnifyMaybe . unifyInterface i) . interfaces) prv >>= \case
    Nothing -> missingInterface i
    Just _  -> pure ()

findMaybeM :: (Foldable t, Monad m) => (a -> m (Maybe b)) -> t a -> m (Maybe b)
findMaybeM p = getAp . fmap getFirst . foldMap (Ap . fmap First . p)


-- Judgements

check :: Algebra sig m => (Check m a ::: Type) -> Elab m a
check (m ::: _T) = case _T of
  T.Comp sig _T -> provide sig $ runCheck m _T
  _T            -> runCheck m _T

newtype Check m a = Check { runCheck :: Type -> Elab m a }
  deriving (Applicative, Functor) via ReaderC Type (Elab m)

mapCheck :: (Elab m a -> Elab m b) -> Check m a -> Check m b
mapCheck f m = Check $ \ _T -> f (runCheck m _T)


newtype Synth m a = Synth { synth :: Elab m (a ::: Type) }

instance Functor (Synth m) where
  fmap f (Synth m) = Synth (first f <$> m)

mapSynth :: (Elab m (a ::: Type) -> Elab m (b ::: Type)) -> Synth m a -> Synth m b
mapSynth f = Synth . f . synth


bind :: (HasCallStack, Has (Throw Err) sig m) => Bind m (Pattern (Name ::: Classifier)) ::: (Quantity, Type) -> Elab m b -> Elab m (Pattern Name, b)
bind (p ::: (q, _T)) m = runBind p _T (\ p' -> (tm <$> p',) <$> ((q, p') |- m))

newtype Bind m a = Bind { runBind :: forall x . Type -> (a -> Elab m x) -> Elab m x }
  deriving (Functor)

mapBind :: (forall x . Elab m x -> Elab m x) -> Bind m a -> Bind m a
mapBind f m = Bind $ \ _A k -> runBind m _A (f . k)
