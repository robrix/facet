{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
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
, printContextEntry
  -- * Algebras
, surface
, explicit
) where

import           Control.Applicative ((<**>))
import           Control.Monad.IO.Class
import           Data.Foldable (foldl', toList)
import           Data.Function (on)
import           Data.List (intersperse)
import           Data.Maybe (fromMaybe)
import           Data.Semigroup (stimes)
import qualified Data.Text as T
import           Facet.Algebra
import           Facet.Name hiding (ann)
import qualified Facet.Pretty as P
import           Facet.Syntax
import           Prelude hiding ((**))
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Terminal as ANSI
import           Silkscreen as P
import           Silkscreen.Printer.Prec hiding (Level)
import qualified Silkscreen.Printer.Prec as P
import           Silkscreen.Printer.Rainbow as P

prettyPrint :: MonadIO m => Print -> m ()
prettyPrint = P.putDoc . getPrint

getPrint :: Print -> PP.Doc ANSI.AnsiStyle
getPrint = PP.reAnnotate terminalStyle . getPrint'

getPrint' :: Print -> PP.Doc Highlight
getPrint' = runRainbow (annotate . Nest) 0 . runPrec Null . doc . group

terminalStyle :: Highlight -> ANSI.AnsiStyle
terminalStyle = \case
  Nest i -> colours !! (i `mod` len)
  Name i -> reverse colours !! (getLevel i `mod` len)
  Op     -> ANSI.color ANSI.Cyan
  Type   -> ANSI.color ANSI.Yellow
  Con    -> ANSI.color ANSI.Red
  Lit    -> ANSI.bold
  Hole   -> ANSI.bold <> ANSI.color ANSI.Black
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


data Print = Print { fvs :: FVs, doc :: Prec Precedence (Rainbow (PP.Doc Highlight)) }

instance Semigroup Print where
  Print v1 d1 <> Print v2 d2 = Print (v1 <> v2) (d1 <> d2)
  stimes n (Print v d) = Print (stimes n v) (stimes n d)

instance Monoid Print where
  mempty = Print mempty mempty

instance Vars Print where
  use l = Print (use l) mempty
  cons l d = Print (cons l (fvs d)) (doc d)
  bind l d = Print (bind l (fvs d)) (doc d)

instance Printer Print where
  type Ann Print = Highlight

  liftDoc0 a = Print mempty (liftDoc0 a)
  liftDoc1 f (Print v d) = Print v (liftDoc1 f d)
  liftDoc2 f (Print v1 d1) (Print v2 d2) = Print (v1 <> v2) (liftDoc2 f d1 d2)

  -- NB: FIXME: these run everything twice which seems bad.
  column    f = Print (fvs (f 0))         (column    (doc . f))
  nesting   f = Print (fvs (f 0))         (nesting   (doc . f))
  pageWidth f = Print (fvs (f Unbounded)) (pageWidth (doc . f))

  enclosing (Print vl dl) (Print vr dr) (Print vx dx) = Print (vl <> vr <> vx) (enclosing dl dr dx)

  brackets (Print v d) = Print v (brackets d)
  braces   (Print v d) = Print v (braces   d)
  parens   (Print v d) = Print v (parens   d)
  angles   (Print v d) = Print v (angles   d)
  squotes  (Print v d) = Print v (squotes  d)
  dquotes  (Print v d) = Print v (dquotes  d)

instance PrecedencePrinter Print where
  type Level Print = Precedence

  -- FIXME: this is running things twice.
  askingPrec f = Print (fvs (f minBound)) (askingPrec (doc . f))
  localPrec f (Print v d) = Print v (localPrec f d)

instance Show Print where
  showsPrec p = showsPrec p . getPrint

-- FIXME: NO. BAD.
instance Eq Print where
  (==) = (==) `on` show


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
  | Name Level
  | Con
  | Type
  | Op
  | Lit
  | Hole
  | ANSI ANSI.AnsiStyle
  deriving (Eq, Ord, Show)

op :: (Printer p, Ann p ~ Highlight) => p -> p
op = annotate Op


arrow :: (Printer p, Ann p ~ Highlight) => p
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
  . enclose space space

commaSep :: [Print] -> Print
commaSep = encloseSep mempty mempty (comma <> space)

ann :: (PrecedencePrinter p, P.Level p ~ Precedence) => (p ::: p) -> p
ann (n ::: t) = align . prec Ann $ n </> group (align (colon <+> flatAlt space mempty <> t))

evar :: (PrecedencePrinter p, P.Level p ~ Precedence, Ann p ~ Highlight) => Level -> p
evar = setPrec Var . annotate . Name <*> P.lower . getLevel

tvar :: (PrecedencePrinter p, P.Level p ~ Precedence, Ann p ~ Highlight) => Level -> p
tvar = setPrec Var . annotate . Name <*> P.upper . getLevel


prettyMName :: Printer p => MName -> p
prettyMName (n :. s)  = prettyMName n <> pretty '.' <> pretty s
prettyMName (MName s) = pretty s


printContextEntry :: Level -> UName ::: Print -> Print
printContextEntry l (n ::: _T) = ann (intro explicit n l ::: _T)


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

($$*) :: Foldable t => Print -> t Print -> Print
($$*) = fmap group . foldl' ($$)

(>~>) :: ((Pl, Print) ::: Print) -> Print -> Print
((pl, n) ::: t) >~> b = prec FnR (flatAlt (column (\ i -> nesting (\ j -> stimes (j + 3 - i) space))) mempty <> group (align (unPl braces parens pl (space <> ann (setPrec Var n ::: t) <> line))) </> arrow <+> b)


surface :: Algebra Print
surface = Algebra
  { var = \case
    Global _ n -> setPrec Var (pretty n)
    TLocal n d -> name P.upper n d
    Local  n d -> name P.lower n d
    Metavar  d -> setPrec Var (annotate Hole (pretty '?' <> evar (Level (getMeta d))))
    Cons     n -> setPrec Var (annotate Con (pretty n))
  , tintro = name P.upper
  , intro = name P.lower
  , lam = comp . embed . commaSep
  , clause = \ ns b -> embed (setPrec Pattern (vsep (map (unPl_ (braces . tm) tm) ns)) </> arrow) </> b
  -- FIXME: group quantifiers by kind again.
  , fn = \ as b -> foldr (\ (P pl (n ::: _T)) b -> case n of
    Just n -> ((pl, n) ::: _T) >~> b
    _      -> _T --> b) b as
  , app = \ f as -> f $$* fmap (unPl_ braces id) as
  , prd = \ as -> case as of
    [] -> parens mempty
    as -> foldl1 (**) as
  , hole = \ n -> annotate Hole $ pretty '?' <> pretty n
  , _Type = annotate Type $ pretty "Type"
  , _Void = annotate Type $ pretty "Void"
  , _Unit = annotate Type $ pretty "Unit"
  , unit = annotate Con $ pretty "Unit"
  , ann' = tm
  , case' = \ s ps -> embed $ pretty "case" <+> setPrec Expr s </> block (commaSep (map (\ (p, b) -> embed (prec Pattern p </> arrow) </> b) ps))
  , wildcard = pretty '_'
  , pcon = \ n ps -> parens (hsep (annotate Con n:toList ps))
  , tuple = tupled
  , decl = ann
  , defn = \ (a :=: b) -> a </> b
  , data' = block . commaSep
  , module_ = \ (n ::: t :=: ds) -> ann (setPrec Var (prettyMName n) ::: fromMaybe (pretty "Module") t) </> block (embed (vsep (intersperse mempty ds)))
  }
  where
  embed = nest 2 . group
  name f n d = setPrec Var . annotate (Name d) $ if T.null (getUName n) then
    pretty '_' <> f (getLevel d)
  else
    pretty n

-- FIXME: elide unused vars
explicit :: Algebra Print
explicit = Algebra
  { var = \case
    Global _ n -> setPrec Var (pretty n)
    TLocal n d -> name P.upper n d
    Local  n d -> name P.lower n d
    Metavar  d -> setPrec Var (annotate Hole (pretty '?' <> evar (Level (getMeta d))))
    Cons     n -> setPrec Var (annotate Con (pretty n))
  , tintro = name P.upper
  , intro = name P.lower
  , lam = comp . embed . commaSep
  , clause = \ ns b -> group (align (setPrec Pattern (vsep (map (\ (P pl (n ::: _T)) -> group $ unPl braces id pl (maybe n (ann . (n :::)) _T)) ns)) </> arrow)) </> b
  -- FIXME: group quantifiers by kind again.
  , fn = \ as b -> foldr (\ (P pl (n ::: _T)) b -> case n of
    Just n -> ((pl, n) ::: _T) >~> b
    _      -> _T --> b) b as
  , app = \ f as -> group f $$* fmap (group . unPl_ braces id) as
  , prd = \ as -> case as of
    [] -> parens mempty
    as -> foldl1 (**) as
  , hole = \ n -> annotate Hole $ pretty '?' <> pretty n
  , _Type = annotate Type $ pretty "Type"
  , _Void = annotate Type $ pretty "Void"
  , _Unit = annotate Type $ pretty "Unit"
  , unit = annotate Con $ pretty "Unit"
  , ann' = group . tm
  , case' = \ s ps -> embed $ pretty "case" <+> setPrec Expr s </> block (commaSep (map (\ (p, b) -> embed (prec Pattern p </> arrow) </> b) ps))
  , wildcard = pretty '_'
  , pcon = \ n ps -> parens (hsep (annotate Con n:toList ps))
  , tuple = tupled
  , decl = ann
  , defn = \ (a :=: b) -> a </> b
  , data' = block . commaSep
  , module_ = \ (n ::: t :=: ds) -> ann (setPrec Var (prettyMName n) ::: fromMaybe (pretty "Module") t) </> block (embed (vsep (intersperse mempty ds)))
  }
  where
  embed = nest 2 . group
  name f _ d = setPrec Var (annotate (Name d) (cons d (f (getLevel d))))
