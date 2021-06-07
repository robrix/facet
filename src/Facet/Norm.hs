module Facet.Norm
( Norm(..)
, quote
, norm
) where

import Control.Monad (guard)
import Data.Foldable (foldl')
import Data.Function (on)
import Data.Maybe (fromMaybe)
import Data.Monoid
import Data.Text (Text)
import Data.Traversable (mapAccumL)
import Facet.Env
import Facet.Name
import Facet.Pattern
import Facet.Semialign (zipWithM)
import Facet.Snoc
import Facet.Syntax
import Facet.Term

data Norm
  = NString Text
  | NCon RName [Norm]
  | NLam [(Pattern Name, Pattern (Name :=: Norm) -> Norm)]
  | NNe (Var (LName Level)) (Snoc Norm)
  | NDict [RName :=: Norm]
  | NComp [RName :=: Name] (Pattern (Name :=: Norm) -> Norm)

instance Eq Norm where
  (==) = (==) `on` quote 0

instance Ord Norm where
  compare = compare `on` quote 0


quote :: Level -> Norm -> Expr
quote d = \case
  NString s -> XString s
  NCon n sp -> XCon n (quote d <$> sp)
  NLam cs   -> XLam (map (uncurry clause) cs)
  NNe v sp  -> foldl' (\ h -> XApp h . quote d) (XVar (fmap (levelToIndex d) <$> v)) sp
  NDict os  -> XDict (map (fmap (quote d)) os)
  NComp p b -> XComp p (snd (clause (PDict p) b))
  where
  clause p b = let (d', p') = mapAccumL (\ d n -> (succ d, n :=: NNe (Free (LName d n)) Nil)) d p in (p, quote d' (b p'))

norm :: Env Norm -> Expr -> Norm
norm env = \case
  XString s  -> NString s
  XVar v     -> NNe (fmap (indexToLevel (level env)) <$> v) Nil
  XCon n sp  -> NCon n (norm env <$> sp)
  XApp f a   -> norm env f `napp`  norm env a
  XLam cs    -> NLam (map (\ (p, b) -> (p, \ p' -> norm (env |> p') b)) cs)
  XDict os   -> NDict (map (fmap (norm env)) os)
  XLet p v b -> norm (env |> fromMaybe (error "norm: non-exhaustive pattern in let") (match (norm env v) p)) b
  XComp p b  -> NComp p (\ p' -> norm (env |> p') b)


napp :: Norm -> Norm -> Norm
napp f a = case f of
  NLam cs  -> case getFirst (foldMap (\ (p, b) -> First (b <$> match a p)) cs) of
    Just a' -> a'
    Nothing -> error "napp: non-exhaustive patterns in lambda"
  NNe h sp -> NNe h (sp :> a)
  _        -> error "napp: ill-formed application"

match :: Norm -> Pattern Name -> Maybe (Pattern (Name :=: Norm))
match s = \case
  PWildcard -> Just PWildcard
  PVar n    -> Just (PVar (n :=: s))
  PCon n ps -> case s of
    NCon n' fs -> PCon n' <$ guard (n == n') <*> zipWithM match fs ps
    _          -> Nothing
  PDict ps  -> case s of
    NDict os -> PDict <$> zipWithM (\ (n1 :=: o) (n2 :=: p) -> (n1 :=: (p :=: o)) <$ guard (n1 == n2)) os ps
    _        -> Nothing

-- ninst :: Norm -> T.Type -> Norm
-- ninst f t = case f of
--   NTLam _ b -> b t
--   NNe h sp  -> NNe h (sp :> EInst t)
--   _         -> error "ninst: ill-formed instantiation"
