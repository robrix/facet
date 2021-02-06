module Facet.Core.Term
( -- * Patterns
  ValuePattern(..)
, Pattern(..)
, pvar
, pcon
, fill
  -- * Term values
, Value(..)
, global
, free
, var
  -- ** Elimination
, ($$)
, ($$*)
, ($$$)
, ($$$*)
  -- ** Debugging
, showValue
  -- * Term expressions
, Expr(..)
  -- * Quotation
, quote
, eval
) where

import           Control.Monad (guard)
import           Data.Either (fromRight)
import           Data.Foldable (asum, foldl')
import           Data.Semialign.Exts (zipWithM)
import           Data.Text (Text)
import           Data.Traversable (mapAccumL)
import           Data.Void (Void)
import qualified Facet.Core.Type as T
import           Facet.Name
import           Facet.Pretty (toAlpha)
import           Facet.Show
import           Facet.Stack
import           Facet.Syntax
import           GHC.Stack

-- Patterns

data ValuePattern a
  = PWildcard
  | PVar a
  | PCon (Q Name) (Stack (ValuePattern a))
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Pattern a
  = PEff (Q Name) (Stack (ValuePattern a)) a
  | PAll a
  | PVal (ValuePattern a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

pvar :: a -> Pattern a
pvar = PVal . PVar

pcon :: Q Name -> Stack (ValuePattern a) -> Pattern a
pcon n fs = PVal $ PCon n fs


fill :: Traversable t => (b -> (b, c)) -> b -> t a -> (b, t c)
fill f = mapAccumL (const . f)


-- Term values

data Value
  = VTLam (T.Type -> Value)
  | VLam [(Pattern Name, Pattern Value -> Value)]
  | VNe (Var Void Level) (Stack T.Type) (Stack Value)
  | VCon (Q Name) (Stack T.Type) (Stack Value)
  | VString Text
  | VOp (Q Name) (Stack T.Type) (Stack Value)


global :: Q Name -> Value
global = var . Global

free :: Level -> Value
free = var . Free


var :: Var Void Level -> Value
var v = VNe v Nil Nil


-- Elimination

($$) :: HasCallStack => Value -> Value -> Value
VNe h ts es $$ a = VNe h ts (es :> a)
VLam cs     $$ a = case' a cs
VOp h ts es $$ a = VOp h ts (es :> a)
v           $$ a = error $ "can’t apply " <> show (showValue Nil Nil v <+> showValue Nil Nil a)

($$*) :: (HasCallStack, Foldable t) => Value -> t Value -> Value
($$*) = foldl' ($$)

infixl 9 $$, $$*


($$$) :: HasCallStack => Value -> T.Type -> Value
VNe h ts es $$$ t = VNe h (ts :> t) es
VTLam b     $$$ t = b t
VOp h ts es $$$ t = VOp h (ts :> t) es
v           $$$ t = error $ "can’t instantiate " <> show (showValue Nil Nil v <+> T.showType Nil t)

($$$*) :: (HasCallStack, Foldable t) => Value -> t T.Type -> Value
($$$*) = foldl' ($$$)

infixl 9 $$$, $$$*


case' :: HasCallStack => Value -> [(Pattern Name, Pattern Value -> Value)] -> Value
case' s cs = case asum (map (\ (p, f) -> f <$> match s p) cs) of
  Just v -> v
  _      -> error "non-exhaustive patterns in lambda"

match :: Value -> Pattern b -> Maybe (Pattern Value)
match = curry $ \case
  (s, PAll _)  -> Just (PAll s)
  -- FIXME: match effect patterns against computations (?)
  (_, PEff{})  -> Nothing
  (s, PVal p') -> PVal <$> value s p'
  where
  value = curry $ \case
    (_,            PWildcard) -> Just PWildcard
    (s,            PVar _)    -> Just (PVar s)
    -- NB: we’re assuming they’re the same length because they’ve passed elaboration.
    (VCon n' _ fs, PCon n ps) -> PCon n' <$ guard (n == n') <*> zipWithM value fs ps
    (_,            PCon{})    -> Nothing


-- Debugging

showValue :: HasCallStack => Stack ShowP -> Stack ShowP -> Value -> ShowP
showValue tenv env = \case
  VTLam b      -> brace (brace (string (toAlpha alpha (length tenv))) <+> string "->" <+> setPrec 0 (showValue (tenv :> string (toAlpha alpha (length tenv))) env (b (T.free (Level (length tenv))))))
  VLam cs      -> brace (commaSep (map clause cs))
  VNe f ts sp  -> head f $$* (brace . T.showType tenv <$> ts) $$* (setPrec 11 . showValue tenv env <$> sp)
  VCon q ts fs -> qname q $$* (brace . T.showType tenv <$> ts) $$* (setPrec 11 . showValue tenv env <$> fs)
  VString s    -> text s
  VOp f ts sp  -> qname f $$* (brace . T.showType tenv <$> ts) $$* (setPrec 11 . showValue tenv env <$> sp)
  where
  ($$*) = foldl' (\ f a -> prec 10 (f <+> a))
  infixl 9 $$*
  clause (p, b) = pat p <+> string "->" <+> setPrec 0 (showValue tenv env' (b p'))
    where
    ((env', _), p') = mapAccumL (\ (env, d) n -> ((env :> name n, succ d), free d)) (env, Level (length env)) p
  pat = \case
    PAll n      -> bracket (name n)
    PVal p      -> vpat p
    PEff n ps k -> bracket (foldl' (<+>) (qname n) (vpat <$> ps) <+> char ';' <+> name k)
  vpat = \case
    PWildcard -> char '_'
    PVar n    -> name n
    PCon f ps -> paren $ foldl' (<+>) (qname f) (vpat <$> ps)
  alpha = ['A'..'Z']
  head :: Var Void Level -> ShowP
  head = \case
    Global (m :.: n) -> foldr (<.>) (name n) (text <$> m)
    Free v           -> env ! getIndex (levelToIndex (Level (length env)) v)
    Metavar m        -> case m of {}


-- Term expressions

data Expr
  = XVar (Var Void Index)
  | XTLam Expr
  | XLam [(Pattern Name, Expr)]
  | XInst Expr T.TExpr
  | XApp Expr Expr
  | XCon (Q Name) (Stack T.TExpr) (Stack Expr)
  | XString Text
  | XOp (Q Name)
  deriving (Eq, Ord, Show)


-- Quotation

quote :: Level -> Value -> Expr
quote d = \case
  VTLam b      -> XTLam (quote (succ d) (b (T.free d)))
  VLam cs      -> XLam (map (\ (p, b) -> (p, let (d', p') = fill (\ d -> (succ d, free d)) d p in quote d' (b p'))) cs)
  VNe h ts as  -> let h' = XVar (levelToIndex d <$> h) ; h'' = foldl' XInst h' (T.quote d <$> ts) in foldl' XApp h'' (quote d <$> as)
  VCon n ts fs -> XCon n (T.quote d <$> ts) (quote d <$> fs)
  VString s    -> XString s
  VOp n ts sp  -> foldl' XApp (foldl' XInst (XOp n) (T.quote d <$> ts)) (quote d <$> sp)

eval :: HasCallStack => T.Subst -> Stack (Either T.Type Value) -> Expr -> Value
eval subst = go where
  go env = \case
    XVar (Global n)  -> global n
    XVar (Free v)    -> fromRight (error ("type variable at index " <> show v)) (env ! getIndex v)
    XVar (Metavar m) -> case m of {}
    XTLam b          -> VTLam (\ _T -> go (env :> Left _T) b)
    XLam cs          -> VLam (map (\ (p, b) -> (p, \ p -> go (foldl' (\ env' v -> env' :> Right v) env p) b)) cs)
    XInst f a        -> go env f $$$ T.eval subst env a
    XApp  f a        -> go env f $$ go env a
    XCon n ts fs     -> VCon n (T.eval subst env <$> ts) (go env <$> fs)
    XString s        -> VString s
    XOp n            -> VOp n Nil Nil
