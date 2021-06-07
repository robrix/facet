module Facet.Notice.Elab
( -- * Elaboration
  rethrowElabErrors
, rethrowElabWarnings
) where

import           Data.Foldable (foldl')
import           Data.Semigroup (stimes)
import qualified Facet.Carrier.Throw.Inject as L
import qualified Facet.Carrier.Write.Inject as L
import           Facet.Context
import           Facet.Elab as Elab
import qualified Facet.Env as Env
import           Facet.Interface (interfaces)
import           Facet.Name (LName(..))
import           Facet.Notice as Notice hiding (level)
import           Facet.Pretty
import           Facet.Print as Print
import           Facet.Semiring (Few(..), one, zero)
import           Facet.Snoc
import           Facet.Style
import           Facet.Subst (metas)
import           Facet.Syntax
import           Facet.Type.Norm (Classifier(..), apply, free, metavar)
import           GHC.Stack
import           Prelude hiding (unlines)
import           Silkscreen

-- Elaboration

rethrowElabErrors :: Applicative m => Options -> L.ThrowC (Notice (Doc Style)) Err m a -> m a
rethrowElabErrors opts = L.runThrow (pure . rethrow)
  where
  rethrow Err{ source, reason, context, subst, sig, callStack } = Notice.Notice (Just Error) [source] (printErrReason opts printCtx reason)
    [ nest 2 (pretty "Context" <\> concatWith (<\>) ctx)
    , nest 2 (pretty "Metacontext" <\> concatWith (<\>) subst')
    , nest 2 (pretty "Provided interfaces" <\> concatWith (<\>) sig')
    , pretty (prettyCallStack callStack)
    ]
    where
    (_, _, printCtx, ctx) = foldl' combine (0, Env.empty, Env.empty, Nil) (elems context)
    subst' = map (\ (m :=: v) -> getPrint (Print.meta m <+> pretty '=' <+> maybe (pretty '?') (printType opts printCtx) v)) (metas subst)
    sig' = getPrint . printInterface opts printCtx . fmap (apply subst (toEnv context)) <$> (interfaces =<< sig)
    combine (d, env, print, ctx) (m, p) =
      let roundtrip = apply subst env
          binding (n ::: _T) = ann (intro n d ::: mult m (case _T of
            CK _K -> printKind print _K
            CT _T -> printType opts print (roundtrip _T)))
      in  ( succ d
          , env Env.|> ((\ (n ::: _T) -> n :=: free (LName d n)) <$> p)
          , print Env.|> ((\ (n ::: _) -> n :=: intro n d) <$> p)
          , ctx :> getPrint (printPattern opts (binding <$> p)) )
  mult m = if
    | m == zero -> (pretty "0" <+>)
    | m == one  -> (pretty "1" <+>)
    | otherwise -> id


printErrReason :: Options -> Env.Env Print -> ErrReason -> Doc Style
printErrReason opts ctx = group . \case
  FreeVariable n               -> fillSep [reflow "variable not in scope:", pretty n]
  AmbiguousName n qs           -> fillSep [reflow "ambiguous name", pretty n] <\> nest 2 (reflow "alternatives:" <\> unlines (map pretty qs))
  CouldNotSynthesize           -> reflow "could not synthesize a type; try a type annotation"
  ResourceMismatch n e a       -> fillSep [reflow "uses of variable", pretty n, reflow "didn’t match requirements"]
    <> hardline <> pretty "expected:" <+> prettyQ e
    <> hardline <> pretty "  actual:" <+> prettyQ a
    where
    prettyQ = \case
      Zero -> pretty "0"
      One  -> pretty "1"
      Many -> pretty "arbitrarily many"
  Unify r (Exp exp) (Act act) -> reason r
    <> hardline <> pretty "expected:" <> print exp'
    <> hardline <> pretty "  actual:" <> print act'
    where
    reason = \case
      Mismatch   -> pretty "mismatch"
      Occurs v t -> reflow "infinite type:" <+> getPrint (printType opts ctx (metavar v)) <+> reflow "occurs in" <+> getPrint (printSubject opts ctx t)
    exp' = either reflow (getPrint . printSubject opts ctx) exp
    act' = getPrint (printSubject opts ctx act)
    -- line things up nicely for e.g. wrapped function types
    print = nest 2 . (flatAlt (line <> stimes (3 :: Int) space) mempty <>)
  Hole n _T                    ->
    let _T' = getPrint (printSubject opts ctx _T)
    in fillSep [ reflow "found hole", pretty n, colon, _T' ]
  Invariant s -> reflow s
  MissingInterface i -> reflow "could not find required interface" <+> getPrint (printInterface opts ctx i)


rethrowElabWarnings :: L.WriteC (Notice (Doc Style)) Warn m a -> m a
rethrowElabWarnings = L.runWrite inject
  where
  inject Elab.Warn{ source, reason } = Notice.Notice (Just Notice.Warn) [source] (printWarnReason reason) []

printWarnReason :: WarnReason -> Doc Style
printWarnReason = \case
  RedundantCatchAll n -> fillSep [reflow "redundant catch all pattern", pretty n]
  RedundantVariable n -> fillSep [reflow "redundant variable", pretty n]
