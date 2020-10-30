-- | Operations driving the loading and processing of modules.
module Facet.Driver
( Target(..)
, modules_
, targets_
, searchPaths_
  -- * Module loading
, reloadModules
, loadModuleHeader
, loadModule
, resolveName
) where

import           Control.Carrier.Fresh.Church
import           Control.Carrier.Reader
import           Control.Effect.Error
import           Control.Effect.Lens (use, (.=))
import           Control.Effect.State
import           Control.Lens (Lens', at, lens)
import           Control.Monad ((<=<))
import           Control.Monad.IO.Class
import           Data.Foldable (toList)
import           Data.Maybe (catMaybes)
import qualified Data.Set as Set
import qualified Data.Text as TS
import           Data.Traversable (for)
import           Facet.Carrier.Parser.Church
import qualified Facet.Carrier.Throw.Inject as I
import           Facet.Core
import           Facet.Effect.Readline
import           Facet.Effect.Trace
import qualified Facet.Elab as Elab
import           Facet.Graph
import           Facet.Lens
import           Facet.Name
import qualified Facet.Notice as Notice
import           Facet.Notice.Elab (rethrowElabErrors)
import           Facet.Notice.Parser (rethrowParseErrors)
import           Facet.Parser
import           Facet.Pretty
import           Facet.Source
import           Facet.Style
import qualified Facet.Surface as S
import           Silkscreen
import           System.Directory (findFile)
import qualified System.FilePath as FP
import           System.IO.Error
import           Text.Parser.Token (whiteSpace)

data Target = Target
  { modules     :: Graph
  , targets     :: Set.Set MName
  , searchPaths :: Set.Set FilePath
  }

modules_ :: Lens' Target Graph
modules_ = lens modules (\ r modules -> r{ modules })

targets_ :: Lens' Target (Set.Set MName)
targets_ = lens targets (\ r targets -> r{ targets })

searchPaths_ :: Lens' Target (Set.Set FilePath)
searchPaths_ = lens searchPaths (\ r searchPaths -> r{ searchPaths })


-- Module loading

reloadModules :: (Has (Error (Notice.Notice (Doc Style))) sig m, Has Output sig m, Has (State Target) sig m, Has Trace sig m, MonadIO m) => Source -> m ()
reloadModules src = do
  modules <- targets_ ~> \ targets -> do
    -- FIXME: remove stale modules
    -- FIXME: failed module header parses shouldn’t invalidate everything.
    targetHeads <- traverse (loadModuleHeader . Right) (toList targets)
    rethrowGraphErrors (Just src) $ loadOrder (fmap toNode . loadModuleHeader . Right) (map toNode targetHeads)
  let nModules = length modules
  results <- evalFresh 1 $ for modules $ \ (name, path, src, imports) -> do
    i <- fresh
    outputDocLn $ annotate Progress (brackets (ratio i nModules)) <+> nest 2 (group (fillSep [ pretty "Loading", pretty name ]))

    -- FIXME: skip gracefully (maybe print a message) if any of its imports are unavailable due to earlier errors
    (Just <$> loadModule name path src imports) `catchError` \ err -> Nothing <$ outputDocLn (prettyNotice err)
  let nSuccess = length (catMaybes results)
      status
        | nModules == nSuccess = annotate Success (pretty nModules)
        | otherwise            = annotate Failure (ratio nSuccess nModules)
  outputDocLn (fillSep [status, reflow "modules loaded."])
  where
  ratio n d = pretty n <+> pretty "of" <+> pretty d
  toNode (n, path, source, imports) = let imports' = map ((S.name :: S.Import -> MName) . S.out) imports in Node n imports' (n, path, source, imports')

loadModuleHeader :: (Has (State Target) sig m, Has (Throw (Notice.Notice (Doc Style))) sig m, MonadIO m) => Either FilePath MName -> m (MName, FilePath, Source, [S.Ann S.Import])
loadModuleHeader target = do
  path <- case target of
    Left path  -> pure path
    Right name -> resolveName name
  src <- rethrowIOErrors Nothing $ readSourceFromFile path
  -- FIXME: validate that the name matches
  (name', is) <- rethrowParseErrors @Style (runParserWithSource src (runFacet [] (whiteSpace *> moduleHeader)))
  pure (name', path, src, is)

loadModule :: (Has (State Target) sig m, Has (Throw (Notice.Notice (Doc Style))) sig m, Has Trace sig m) => MName -> FilePath -> Source -> [MName] -> m Module
loadModule name path src imports = do
  graph <- use modules_
  let ops = foldMap (operators . snd <=< (`lookupM` graph)) imports
  m <- rethrowParseErrors @Style (runParserWithSource src (runFacet (map makeOperator ops) (whole module')))
  m <- rethrowElabErrors src . runReader graph $ Elab.elabModule m
  modules_.at name .= Just (Just path, m)
  pure m

resolveName :: (Has (State Target) sig m, MonadIO m) => MName -> m FilePath
resolveName name = do
  searchPaths <- use searchPaths_
  let namePath = toPath name FP.<.> ".facet"
  path <- liftIO $ findFile (toList searchPaths) namePath
  case path of
    Just path -> pure path
    Nothing   -> liftIO $ ioError $ mkIOError doesNotExistErrorType "loadModule" Nothing (Just namePath)
  where
  toPath (name :. component) = toPath name FP.</> TS.unpack component
  toPath (MName component)   = TS.unpack component


-- Errors

rethrowIOErrors :: (Has (Throw (Notice.Notice (Doc Style))) sig m, MonadIO m) => Maybe Source -> IO a -> m a
rethrowIOErrors src m = liftIO (tryIOError m) >>= either (throwError . ioErrorToNotice src) pure

ioErrorToNotice :: Maybe Source -> IOError -> Notice.Notice (Doc Style)
ioErrorToNotice src err = Notice.Notice (Just Notice.Error) src (group (reflow (show err))) []

rethrowGraphErrors :: Maybe Source -> I.ThrowC (Notice.Notice (Doc Style)) GraphErr m a -> m a
rethrowGraphErrors src = I.runThrow formatGraphErr
  where
  formatGraphErr (CyclicImport path) = Notice.Notice (Just Notice.Error) src (reflow "cyclic import") (map pretty (toList path))
