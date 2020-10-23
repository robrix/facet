module Facet.Eval
( eval
) where

import Control.Effect.Reader
import Facet.Core
import Facet.Graph
import Facet.Syntax

-- FIXME: erase terms before evaluating.
eval :: (Has (Reader Graph) sig m, Has (Reader Module) sig m) => Value -> m Value
eval = \case
  VNeut h sp -> do
    sp' <- traverse evalSp sp
    mod <- ask
    graph <- ask
    case h of
      Global (q ::: _)
        | Just (d ::: _) <- lookupQ q mod graph
        , DTerm v <- d
        -> pure $ elimN v sp'
      _ -> pure $ VNeut h sp'

  v          -> pure v
  where
  evalSp = \case
    EApp a -> EApp <$> traverse eval a
    e      -> pure e
