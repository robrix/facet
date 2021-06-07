module Facet.Term
( -- * Term expressions
  Expr(..)
, TExpr(..)
, Fields(..)
) where

import Data.Bifunctor (bimap)
import Data.Text (Text)
import Facet.Name
import Facet.Pattern
import Facet.Syntax

-- Term expressions

data Expr
  = XVar (Var (LName Index))
  | XLam [(Pattern Name, Expr)]
  | XApp Expr Expr
  | XCon RName [Expr]
  | XString Text
  | XDict [RName :=: Expr]
  | XLet (Pattern Name) Expr Expr
  | XComp [RName :=: Name] Expr -- ^ NB: the first argument is a specialization of @'Pattern' 'Name'@ to the 'PDict' constructor
  deriving (Eq, Ord, Show)

class TExpr expr where
  xvar :: T (Var (LName Index)) a -> expr a

  xlam :: [(T (Pattern Name) a, expr b)] -> expr (a -> b)

  xapp :: expr (a -> b) -> expr a -> expr b

  infixl 9 `xapp`

  xcon :: Fields expr fs => RName -> fs -> expr fs

  xstring :: Text -> expr Text

  xlet :: T (Pattern Name) t -> expr t -> expr u -> expr u

instance TExpr (T Expr) where
  xvar = T . XVar . getT

  xlam ps = T (XLam (map (bimap getT getT) ps))

  xapp (T f) (T a) = T (f `XApp` a)

  xcon n b = T (XCon n (foldFields (pure . getT) b))

  xstring = T . XString

  xlet (T p) (T v) (T b) = T (XLet p v b)


class Fields f fs where
  foldFields :: Monoid m => (forall t . f t -> m) -> fs -> m

instance Fields f () where
  foldFields _ _ = mempty

instance Fields f fs => Fields f (f t, fs) where
  foldFields alg = mappend . alg . fst <*> foldFields alg . snd
