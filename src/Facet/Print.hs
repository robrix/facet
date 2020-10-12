{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Print
( prettyPrint
, getPrint
, terminalStyle
, Print(..)
, Precedence(..)
, evar
, tvar
  -- * Interpreters
, printCoreValue
, printBinding
, printContextEntry
, printSurfaceType
, printSurfaceExpr
, printSurfaceClause
, printCorePattern
, printSurfacePattern
, printSurfaceDecl
, printCoreModule
, printSurfaceModule
) where

import           Control.Applicative (liftA2, (<**>))
import           Control.Monad ((<=<))
import           Control.Monad.IO.Class
import           Data.Bifunctor (bimap, first)
import           Data.Foldable (foldl')
import           Data.List (intersperse)
import           Data.List.NonEmpty (NonEmpty)
import           Data.Monoid (First(..))
import           Data.Semigroup (stimes)
import           Data.Text (Text)
import qualified Data.Text as T
import           Data.Traversable (mapAccumL)
import qualified Facet.Context as Ctx
import qualified Facet.Core.Module as CM
import qualified Facet.Core.Pattern as CP
import qualified Facet.Core.Value as CV
import qualified Facet.Name as N
import qualified Facet.Pretty as P
import           Facet.Stack
import qualified Facet.Surface.Decl as SD
import qualified Facet.Surface.Expr as SE
import qualified Facet.Surface.Module as SM
import qualified Facet.Surface.Pattern as SP
import qualified Facet.Surface.Type as ST
import           Facet.Syntax
import           Prelude hiding ((**))
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Terminal as ANSI
import qualified Silkscreen as P
import           Silkscreen.Printer.Prec hiding (Printer)
import           Silkscreen.Printer.Rainbow hiding (Printer)

prettyPrint :: MonadIO m => Print -> m ()
prettyPrint = P.putDoc . getPrint

getPrint :: Print -> PP.Doc ANSI.AnsiStyle
getPrint = PP.reAnnotate terminalStyle . getPrint'

getPrint' :: Print -> PP.Doc Highlight
getPrint' = runRainbow (annotate . Nest) 0 . runPrec Null . runPrint . group

terminalStyle :: Highlight -> ANSI.AnsiStyle
terminalStyle = \case
  Nest i -> colours !! (i `mod` len)
  Name   -> mempty
  Op     -> ANSI.color ANSI.Cyan
  Type   -> ANSI.color ANSI.Yellow
  Con    -> ANSI.color ANSI.Red
  Lit    -> ANSI.bold
  ANSI s -> s
  where
  colours =
    [ ANSI.Red
    , ANSI.Green
    , ANSI.Yellow
    , ANSI.Blue
    , ANSI.Magenta
    , ANSI.Cyan
    ]
    <**>
    [ANSI.color, ANSI.colorDull]
  len = length colours


newtype Print = Print { runPrint :: Prec Precedence (Rainbow (PP.Doc Highlight)) }
  deriving (Monoid, PrecedencePrinter, P.Printer, Semigroup)

instance Show Print where
  showsPrec p = showsPrec p . getPrint


data Precedence
  = Null
  | Ann
  | FnR
  | FnL
  | Comp
  | Expr
  | Pattern
  | AppL
  | AppR
  | Var
  deriving (Bounded, Eq, Ord, Show)

data Highlight
  = Nest Int
  | Name
  | Con
  | Type
  | Op
  | Lit
  | ANSI ANSI.AnsiStyle
  deriving (Eq, Ord, Show)

op :: (P.Printer p, Ann p ~ Highlight) => p -> p
op = annotate Op


arrow :: (P.Printer p, Ann p ~ Highlight) => p
arrow = op (pretty "->")

comp :: Print -> Print
comp
  = block
  . prec Comp

block :: Print -> Print
block
  = group
  . align
  . braces
  . enclose space line

commaSep :: [Print] -> Print
commaSep = encloseSep mempty mempty (comma <> space)

cases :: [Print] -> Print -> Print
cases vs b = foldr (\ v r -> prec Pattern v <+> r) (arrow <+> group (nest 2 (line' <> prec Expr b))) vs

ann :: P.Printer p => (p ::: p) -> p
ann (n ::: t) = n </> group (align (colon <+> flatAlt space mempty <> t))

var :: (PrecedencePrinter p, Level p ~ Precedence, Ann p ~ Highlight) => p -> p
var = setPrec Var . annotate Name

evar :: (PrecedencePrinter p, Level p ~ Precedence, Ann p ~ Highlight) => Int -> p
evar = var . P.evar

tvar :: (PrecedencePrinter p, Level p ~ Precedence, Ann p ~ Highlight) => Int -> p
tvar = var . P.tvar


prettyMName :: P.Printer p => N.MName -> p
prettyMName (n N.:. s)  = prettyMName n <> pretty '.' <> pretty s
prettyMName (N.MName s) = pretty s

prettyQName :: PrecedencePrinter p => N.QName -> p
prettyQName (mname N.:.: n) = prettyMName mname <> pretty '.' <> pretty n


printCoreValue :: Monad m => CV.Value m Print -> m Print
printCoreValue = go (N.Level 0)
  where
  go d = \case
    CV.Type     -> pure _Type
    CV.Void     -> pure _Void
    CV.TUnit    -> pure _Unit
    CV.Unit     -> pure _Unit
    t CV.:=> b  -> do
      let n' = name (tm t) d
      t' <- go d (ty t)
      b' <- go (N.incrLevel d) =<< b (CV.bound n')
      pure $ (n' ::: t') >~> b'
    CV.TLam n b -> let n' = name n d in lam (braces n') <$> (go (N.incrLevel d) =<< b (CV.bound n'))
    CV.Lam  n b -> let n' = name n d in lam         n'  <$> (go (N.incrLevel d) =<< b (CV.bound n'))
    f CV.:$ as  -> (either cfree id f $$*) <$> traverse (go d) as
    a CV.:-> b  -> (-->) <$> go d a <*> go d b
    CV.TPrd l r -> (**)  <$> go d l <*> go d r
    CV.Prd  l r -> (**)  <$> go d l <*> go d r
    CV.Case s p -> case' <$> go d s <*> traverse (clause d) p
  name n d = cbound n tvar d
  case' s cs = pretty "case" <+> s <+> block (commaSep cs)
  clause d (p, b) = do
    let p' = snd (mapAccumL (\ d n -> (N.incrLevel d, let n' = name n d in (n', CV.bound n'))) d p)
    b' <- go (N.incrLevel d) =<< b (snd <$> p')
    pure $ printCorePattern (fst <$> p') <+> arrow <+> b'

printBinding :: Ctx.Context Print -> N.Level -> Print
-- FIXME: there’s no way to recover whether this was a term or type variable binding.
printBinding ctx l = prec Ann $ printContextEntry l (ctx Ctx.! N.levelToIndex (Ctx.level ctx) l)

printContextEntry :: N.Level -> N.UName ::: Print -> Print
printContextEntry l (n ::: _T) = ann (cbound n tvar l ::: _T)


printSurfaceType :: (Foldable f, Functor f) => Stack Print -> ST.Type f a -> Print
printSurfaceType = go
  where
  go env = \case
    ST.Free n  -> sfree n
    ST.Bound n -> env ! N.getIndex n
    ST.Hole n  -> hole n
    ST.Type    -> _Type
    ST.Void    -> _Void
    ST.Unit    -> _Unit
    t ST.:=> b ->
      let (t', b') = splitr (ST.unForAll <=< extract) b
      in forAlls (map (first sbound) (t:t')) (foldMap (go (env:>sbound (tm t))) b')
    f ST.:$  a ->
      let (f', a') = splitl (ST.unApp <=< extract) f
      in foldMap (go env) f' $$* fmap (foldMap (go env)) (a' :> a)
    a ST.:-> b -> foldMap (go env) a --> foldMap (go env) b
    l ST.:*  r -> foldMap (go env) l **  foldMap (go env) r

sfree :: N.DName -> Print
sfree = var . pretty

cfree :: N.QName -> Print
cfree = var . prettyQName


sbound :: N.UName -> Print
sbound = var . pretty

cbound :: N.UName -> (Int -> Print) -> N.Level -> Print
cbound h printLevel level
  | T.null (N.getUName h) = printLevel (N.getLevel level)
  | otherwise             = pretty h <> pretty (N.getLevel level)


hole :: Text -> Print
hole n = pretty '?' <> pretty n


_Type, _Void, _Unit :: Print
_Type = annotate Type $ pretty "Type"
_Void = annotate Type $ pretty "Void"
_Unit = annotate Type $ pretty "Unit"

($$), (-->), (**) :: Print -> Print -> Print
f $$ a = askingPrec $ \case
  AppL -> op
  _    -> group op
  where
  -- FIXME: lambdas get parenthesized on the left
  op = leftAssoc AppL AppR (\ f a -> f <> nest 2 (line <> a)) f a

-- FIXME: I think the precedence is being reset by the parens or something and thus we aren’t parenthesizing the body?
(-->) = rightAssoc FnR FnL (\ a b -> group (align a) </> arrow <+> b)

-- FIXME: left-flatten products
l ** r = tupled [l, r]

($$*) :: Print -> Stack Print -> Print
($$*) = fmap group . foldl' ($$)

(>~>) :: (Print ::: Print) -> Print -> Print
(n ::: t) >~> b = prec FnR (flatAlt (column (\ i -> nesting (\ j -> stimes (j + 3 - i) space))) mempty <> group (align (braces (space <> ann (var n ::: t) <> line))) </> arrow <+> b)

forAlls :: (Foldable f, Functor f) => [Print ::: f (ST.Type f a)] -> Print -> Print
forAlls ts b = foldr go b (groupByType ST.aeq ts)
  where
  -- FIXME: this is horribly wrong and probably going to crash
  go (t, ns) b = (commaSep ns ::: foldMap (printSurfaceType Nil) t) >~> b

groupByType :: (Foldable f, Functor f) => (t -> t -> Bool) -> [(n ::: f t)] -> [(f t, [n])]
groupByType eq = \case
  []   -> []
  x:xs -> (ty x, tm x:map tm ys) : groupByType eq zs
    where
    (ys,zs) = span (and . liftA2 eq (extract (ty x)) . extract . ty) xs


printSurfaceExpr :: (Foldable f, Functor f) => Stack Print -> SE.Expr f a -> Print
printSurfaceExpr = go
  where
  go env = \case
    SE.Free n  -> sfree n
    SE.Bound n -> env ! N.getIndex n
    SE.Hole n  -> hole n
    f SE.:$  a ->
      let (f', a') = splitl (SE.unApp <=< extract) f
      in foldMap (go env) f' $$* fmap (foldMap (go env)) (a' :> a)
    SE.Unit    -> unit
    l SE.:*  r -> foldMap (go env) l **  foldMap (go env) r
    SE.Comp c  -> comp . (`foldMap` c) $ \case
      SE.Expr e     -> prec Expr $ foldMap (printSurfaceExpr env) e
      SE.Clauses cs -> commaSep (map (uncurry (printSurfaceClause env)) cs)
      -- comp . commaSep $ map (foldMap (printSurfaceClause env)) c

printSurfaceClause :: (Foldable f, Functor f) => Stack Print -> NonEmpty (f (SP.Pattern f N.UName)) -> f (SE.Expr f a) -> Print
printSurfaceClause env ps b = foldMap (foldMap printSurfacePattern) ps' <+> arrow <> group (nest 2 (line <> prec Expr (foldMap (printSurfaceExpr env') b)))
  where
  ps' = fmap (fmap sbound) <$> ps
  env' = foldl (foldl (foldl (:>))) env ps'

printCorePattern :: CP.Pattern Print -> Print
printCorePattern = prec Pattern . \case
  CP.Wildcard -> pretty '_'
  CP.Var n    -> n
  CP.Tuple p  -> tupled (map printCorePattern p)

printSurfacePattern :: (Foldable f, Functor f) => SP.Pattern f Print -> Print
printSurfacePattern p = prec Pattern $ case p of
  SP.Wildcard -> pretty '_'
  SP.Var n    -> n
  SP.Tuple p  -> tupled (map (foldMap printSurfacePattern) p)

-- FIXME: Use _ in binding positions for unused variables
lam :: Print -> Print -> Print
lam n = lams [n]

lams :: [Print] -> Print -> Print
lams ns b = askingPrec $ \case
  Comp -> cases ns b
  _    -> comp (cases ns b)

unit :: Print
unit = annotate Con $ pretty "Unit"


printSurfaceDecl :: (Foldable f, Functor f) => SD.Decl f a -> Print
printSurfaceDecl = go Nil
  where
  go env = \case
    t SD.:=  e -> foldMap (printSurfaceType env) t .= foldMap (printSurfaceExpr env) e
    t SD.:=> b ->
      let (t', b') = splitr (SD.unForAll <=< extract) b
          ts = map (first sbound) (t:t')
      in forAlls ts (foldMap (go (foldl (\ as (a:::_) -> as :> a) env ts)) b')
    t SD.:-> b -> bimap sbound (foldMap (printSurfaceType env)) t >-> foldMap (go (env:>sbound (tm t))) b

extract :: Foldable f => f t -> Maybe t
extract = getFirst . foldMap (First . Just)


-- FIXME: it would be nice to ensure that this gets wrapped if the : in the same decl got wrapped.
(.=) :: Print -> Print -> Print
t .= b = t </> b

(>->) :: (Print ::: Print) -> Print -> Print
(n ::: t) >-> b = prec FnR (group (align (parens (ann (n ::: t)))) </> arrow <+> b)


printCoreModule :: Monad m => CM.Module m N.Level -> m Print
printCoreModule (CM.Module n ds)
  = module' n <$> traverse (\ (n, d ::: t) -> (</>) . ann . (cfree n :::) <$> CV.foldContext printBinding printCoreValue Ctx.empty t <*> printCoreDef d) ds

printCoreDef :: Monad m => CM.Def m N.Level -> m Print
printCoreDef = \case
  CM.DTerm b  -> CV.foldContext printBinding printCoreValue Ctx.empty b
  CM.DType b  -> CV.foldContext printBinding printCoreValue Ctx.empty b
  CM.DData cs -> block . commaSep <$> traverse (fmap ann . traverse (CV.foldContext printBinding printCoreValue Ctx.empty) . first pretty) cs


printSurfaceModule :: (Foldable f, Functor f) => SM.Module f a -> Print
printSurfaceModule (SM.Module n ds) = module' n (map (uncurry printSurfaceDef) ds)

printSurfaceDef :: (Foldable f, Functor f) => N.DName -> f (SD.Decl f a) -> Print
printSurfaceDef n d = def (sfree n) (foldMap printSurfaceDecl d)


module' :: N.MName -> [Print] -> Print
module' n b = ann (var (prettyMName n) ::: pretty "Module") </> block (vsep (intersperse line b))

def :: Print -> Print -> Print
def n b = group $ ann (n ::: b)
