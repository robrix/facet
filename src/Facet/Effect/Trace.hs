{-# LANGUAGE GADTs #-}
module Facet.Effect.Trace
( -- * Trace effect
  trace
, tracePretty
, callStack
, Message
, Trace(..)
  -- * Re-exports
, Algebra
, Has
, run
) where

import Control.Algebra
import Facet.Pretty
import Facet.Stack
import Facet.Style

trace :: Has Trace sig m => Message -> m a -> m a
trace s m = send (Trace s m)

tracePretty :: (Has Trace sig m, Pretty b) => b -> m a -> m a
tracePretty = trace . pretty

-- FIXME: Text, probably
callStack :: Has Trace sig m => m (Stack Message)
callStack = send CallStack

type Message = Doc Style

-- FIXME: timing
-- FIXME: profiling
-- FIXME: logging
-- FIXME: attach haskell source refs to traces
-- FIXME: attach facet source refs to traces of elaboration, &c.
-- FIXME: attach _arbitrary_ data to traces?
data Trace m k where
  Trace :: Message -> m a -> Trace m a
  CallStack :: Trace m (Stack Message)
