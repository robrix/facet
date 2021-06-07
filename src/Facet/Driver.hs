-- | Operations driving the loading and processing of modules.
module Facet.Driver
( Target(..)
, modules_
, targets_
, searchPaths_
, defaultTarget
, kernel
  -- * Module loading
, reloadModules
, ModuleHeader(..)
, imports_
, headerNode
, loadModuleHeader
, loadModule
, storeModule
, resolveName
  -- * Errors
, rethrowIOErrors
, rethrowGraphErrors
) where

import           Control.Algebra
import           Control.Carrier.Reader
import           Control.Effect.Error
import           Control.Effect.Lens (use, uses, (.=))
import           Control.Effect.State
import           Control.Lens (Lens, Lens', at, lens, (^.))
import           Control.Monad.IO.Class
import           Data.Foldable (toList)
import           Data.Maybe (catMaybes)
import qualified Data.Set as Set
import qualified Data.Text as TS
import           Data.Traversable (for)
import           Facet.Carrier.Parser.Church
import qualified Facet.Carrier.Throw.Inject as I
import           Facet.Effect.Readline
import           Facet.Effect.Write
import qualified Facet.Elab.Term as Elab
import           Facet.Graph
import           Facet.Lens
import           Facet.Module hiding (Import(name), imports, imports_)
import           Facet.Name
import qualified Facet.Notice as Notice
import           Facet.Notice.Elab (rethrowElabErrors, rethrowElabWarnings)
import           Facet.Notice.Parser (rethrowParseErrors)
import           Facet.Parser
import           Facet.Pretty
import           Facet.Print (Options)
import           Facet.Snoc
import           Facet.Source
import           Facet.Style
import qualified Facet.Surface as Import (Import(..))
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

defaultTarget :: Target
defaultTarget = Target
  { modules = singleton Nothing kernel
  , targets = mempty
  , searchPaths = mempty
  }


kernel :: Module
kernel = Module kernelName [] [] $ Scope mempty
  -- FIXME: include things like Type and Interface
  where
  kernelName = fromList [U (TS.pack "Kernel")]


-- Module loading

reloadModules :: (Has (Error (Notice.Notice (Doc Style)) :+: Output :+: State Options :+: State Target :+: Write (Notice.Notice (Doc Style))) sig m, MonadIO m) => m ()
reloadModules = do
  searchPaths <- uses searchPaths_ toList
  modules_ .= singleton Nothing kernel
  modules <- targets_ ~> \ targets -> do
    -- FIXME: remove stale modules
    -- FIXME: only reload changed modules
    -- FIXME: failed module header parses shouldn’t invalidate everything.
    -- FIXME: allow later modules to load despite failures if at least types have elaborated correctly
    targetHeads <- traverse (loadModuleHeader searchPaths . Right) (toList targets)
    rethrowGraphErrors [] $ loadOrder (fmap headerNode . loadModuleHeader searchPaths . Right) (map headerNode targetHeads)
  let nModules = length modules
  results <- for (zip [1..] modules) $ \ (i, h@(ModuleHeader name src _)) -> do
    graph <- use modules_
    let loaded = traverse (\ name -> graph^.at name >>= snd) h
    case loaded of
      Just loaded -> (Just <$> do
        outputDocLn $ annotate Progress (brackets (ratio (i :: Int) nModules)) <+> nest 2 (group (fillSep [ pretty "Loading", prettyMName name ]))
        storeModule name (path src) =<< loadModule graph loaded)
        `catchError` \ err -> Nothing <$ outputDocLn (prettyNotice err)
      Nothing -> do
        outputDocLn $ annotate Progress (brackets (ratio i nModules)) <+> nest 2 (group (fillSep [ pretty "Skipping", prettyMName name ]))
        pure Nothing
  let nSuccess = length (catMaybes results)
      status
        | nModules == nSuccess = annotate Success (pretty nModules)
        | otherwise            = annotate Failure (ratio nSuccess nModules)
  outputDocLn (fillSep [status, reflow "modules loaded."])
  where
  ratio n d = pretty n <+> pretty "of" <+> pretty d

data ModuleHeader a = ModuleHeader
  { moduleName :: MName
  , source     :: Source
  , imports    :: [a]
  }
  deriving (Foldable, Functor, Traversable)

imports_ :: Lens (ModuleHeader a) (ModuleHeader b) [a] [b]
imports_ = lens imports (\ h imports -> h{ imports })

headerNode :: ModuleHeader MName -> Node (ModuleHeader MName)
headerNode h@(ModuleHeader n _ imports) = Node n imports h

loadModuleHeader :: (Has (Output :+: Throw (Notice.Notice (Doc Style))) sig m, MonadIO m) => [FilePath] -> Either FilePath MName -> m (ModuleHeader MName)
loadModuleHeader searchPaths target = do
  path <- case target of
    Left path  -> pure path
    Right name -> resolveName searchPaths name
  src <- rethrowIOErrors [] $ readSourceFromFile path
  -- FIXME: validate that the name matches
  (name', is) <- rethrowParseErrors @_ @Style (runParserWithSource src (runFacet [] (whiteSpace *> moduleHeader)))
  pure (ModuleHeader name' src (map (Import.name . S.out) is))

loadModule :: Has (Output :+: State Options :+: Throw (Notice.Notice (Doc Style)) :+: Write (Notice.Notice (Doc Style))) sig m => Graph -> ModuleHeader Module -> m Module
loadModule graph (ModuleHeader _ src imports) = do
  let ops = foldMap (\ m -> map (\ (op, assoc) -> (name m, op, assoc)) (operators m)) imports
  m <- rethrowParseErrors @_ @Style (runParserWithSource src (runFacet (map makeOperator ops) (whole module')))
  opts <- get
  rethrowElabWarnings . rethrowElabErrors opts . runReader graph . runReader src $ Elab.elabModule m

storeModule :: Has (State Target) sig m => MName -> Maybe FilePath -> Module -> m ()
storeModule name path m = modules_ .at name .= Just (path, Just m)

resolveName :: (Has (Throw (Notice.Notice (Doc Style))) sig m, MonadIO m) => [FilePath] -> MName -> m FilePath
resolveName searchPaths name = do
  let namePath = toPath name FP.<.> ".facet"
  path <- liftIO $ findFile searchPaths namePath
  case path of
    Just path -> pure path
    Nothing   -> throwError @(Notice.Notice (Doc Style)) $ Notice.Notice (Just Notice.Error) [] (fillSep [pretty "module", squotes (prettyMName name), reflow "could not be found."]) $ case searchPaths of
      [] -> []
      _  -> [ nest 2 (reflow "search paths:" <\> concatWith (<\>) (map pretty searchPaths)) ]
  where
  toPath components = foldr1 (FP.</>) (unpack <$> components)
  unpack = \case
    U n -> TS.unpack n
    O o -> formatOp (\ a b -> a <> " " <> b) TS.unpack "_" o


-- Errors

rethrowIOErrors :: (Has (Throw (Notice.Notice (Doc Style))) sig m, MonadIO m) => [Source] -> IO a -> m a
rethrowIOErrors refs m = liftIO (tryIOError m) >>= either (throwError . ioErrorToNotice refs) pure

ioErrorToNotice :: [Source] -> IOError -> Notice.Notice (Doc Style)
ioErrorToNotice refs err = Notice.Notice (Just Notice.Error) refs (group (reflow (show err))) []

rethrowGraphErrors :: Applicative m => [Source] -> I.ThrowC (Notice.Notice (Doc Style)) GraphErr m a -> m a
rethrowGraphErrors refs = I.runThrow (pure . formatGraphErr)
  where
  formatGraphErr (CyclicImport path) = Notice.Notice (Just Notice.Error) refs (reflow "cyclic import") (map prettyMName (toList path))
