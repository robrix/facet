{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
module Facet.REPL
( repl
) where

import           Control.Algebra
import           Control.Applicative ((<|>))
import           Control.Carrier.Empty.Church
import           Control.Carrier.Error.Church
import           Control.Carrier.Fail.Either
import           Control.Carrier.Reader
import           Control.Carrier.State.Church
import           Control.Effect.Lens (use, uses, (%=))
import           Control.Exception (handle)
import           Control.Lens (Lens', lens, (&), (.~))
import           Control.Monad (unless, (<=<))
import           Control.Monad.IO.Class
import           Data.Char
import           Data.Colour.RGBSpace.HSL (hsl)
import           Data.Foldable (toList)
import qualified Data.Map as Map
import           Data.Semigroup (stimes)
import qualified Data.Set as Set
import           Data.Text (Text)
import           Facet.Carrier.Parser.Church hiding (Input)
import           Facet.Carrier.Readline.Haskeline
import qualified Facet.Carrier.Throw.Inject as I
import           Facet.Carrier.Write.General
import qualified Facet.Carrier.Write.Inject as I
import           Facet.Driver
import qualified Facet.Elab as Elab
import qualified Facet.Elab.Term as Elab
import qualified Facet.Elab.Type as Elab
import           Facet.Eval as E
import           Facet.Graph
import           Facet.Interface as I
import           Facet.Lens
import           Facet.Module
import           Facet.Name as Name
import qualified Facet.Notice as Notice
import           Facet.Notice.Elab
import           Facet.Notice.Parser
import           Facet.Parser as Parser
import           Facet.Pretty
import           Facet.Print as Print hiding (meta)
import           Facet.REPL.Parser
import           Facet.Snoc
import           Facet.Source (Source(..), sourceFromString)
import           Facet.Style as Style
import qualified Facet.Surface as S
import           Facet.Syntax
import           Facet.Term (Expr)
import           Prelude hiding (span, unlines)
import           Silkscreen as S hiding (Ann, line)
import           System.Console.ANSI
import           System.Directory
import           System.Exit
import           Text.Parser.Char hiding (space)
import           Text.Parser.Combinators
import           Text.Parser.Token hiding (brackets, comma)

repl :: [FilePath] -> IO ExitCode
repl searchPaths
  = handle @IOError (\ e -> ExitFailure 1 <$ print e)
  . fmap (const ExitSuccess)
  . runReadlineWithHistory
  . evalState (defaultREPLState & target_.searchPaths_ .~ Set.fromList searchPaths)
  . evalState quietOptions
  . evalEmpty
  $ loop


data REPL = REPL
  { line           :: Int
  , promptFunction :: Int -> IO String
  , localDefs      :: Module -- ^ The module where definitions made in the REPL live. Not a part of modules.
  -- FIXME: generalize this to support multiple targets.
  , target         :: Target
  }

line_ :: Lens' REPL Int
line_ = lens line (\ r line -> r{ line })

localDefs_ :: Lens' REPL Module
localDefs_ = lens localDefs (\ r localDefs -> r{ localDefs })

target_ :: Lens' REPL Target
target_ = lens target (\ r target -> r{ target })

defaultREPLState :: REPL
defaultREPLState = REPL
  { line           = 0
  , promptFunction = defaultPromptFunction
  , localDefs
  , target = defaultTarget
  }
  where
  localDefs = Module (fromList ["(interactive)"]) [] [] mempty

defaultPromptFunction :: Int -> IO String
defaultPromptFunction _ = pure $ setTitleCode "facet" <> "\STX" <> bold <> cyan <> "λ " <> plain
  where
  bold = setSGRCode [setBold] <> "\STX"
  cyan = setSGRCode [setRGB (hsl 300 1 0.5)] <> "\STX"
  plain = setSGRCode [] <> "\STX"


loop :: (Has (Empty :+: Input :+: Output :+: State Options :+: State REPL) sig m, MonadIO m) => m ()
loop = do
  -- FIXME: handle interrupts
  resp <- prompt
  runWrite (outputDocLn . prettyNotice) . (either outputStrLn pure <=< runFail) . runError (outputDocLn . prettyNotice) pure $ case resp of
    Just src -> do
      graph <- use (target_.modules_)
      targets <- use (target_.targets_)
      let ops = foldMap (\ name -> lookupM name graph >>= maybe [] pure . snd >>= map (\ (op, assoc) -> (name, op, assoc)) . operators) (toList targets)
      action <- rethrowParseErrors @_ @Style (runParserWithSource src (runFacet (map (\ (n, a, b) -> makeOperator (n, a, b)) ops) commandParser))
      runReader src $ runAction action
    Nothing  -> pure ()
  loop
  where
  commandParser = whole (parseCommands commands <|> showEval <$> expr)


-- TODO:
-- - multiline
-- - breakpoints
-- - shell commands
commands :: Commands Action
commands = choice
  [ command ["help", "h", "?"]  "display this list of commands"      Nothing        $ pure (Action (outputDocLn helpDoc))
  , command ["quit", "q"]       "exit the repl"                      Nothing        $ pure (Action empty)
  , command ["show"]            "show compiler state"                (Just "field") $ choice
    [ showPaths   <$ symbol "paths"
    , showModules <$ symbol "modules"
    , showTargets <$ symbol "targets"
    ]
  , command ["add"]             "add a module/path to the repl"      (Just "item")  $ choice
    [ addPath   <$ symbol "path"   <*> path'
    , addTarget <$ symbol "target" <*> some mname
    ]
  , command ["remove", "rm"]    "remove a module/path from the repl" (Just "item")  $ choice
    [ removePath   <$ symbol "path"   <*> path'
    , removeTarget <$ symbol "target" <*> some mname
    ]
  , command ["reload", "r"]     "reload the loaded modules"          Nothing        $ pure (Action (target_ `zoom` reloadModules))
  , command ["type", "t"]       "show the type of <expr>"            (Just "expr")
    $ showType <$> runFacet [] expr
  , command ["kind", "k"]       "show the kind of <type>"            (Just "type")
    $ showKind <$> runFacet [] Parser.type'
  ]

path' :: TokenParsing p => p FilePath
path' = stringLiteral <|> some (satisfy (not . isSpace))


newtype Action = Action { runAction :: forall sig m . (Has (Empty :+: Error (Notice.Notice (Doc Style)) :+: Output :+: Reader Source :+: State Options :+: State REPL :+: I.Write (Notice.Notice (Doc Style))) sig m, MonadFail m, MonadIO m) => m () }


showPaths, showModules, showTargets :: Action

showPaths   = Action $ do
  dir <- liftIO getCurrentDirectory
  outputDocLn $ nest 2 $ reflow "current working directory:" </> pretty dir
  searchPaths <- uses (target_.searchPaths_) toList
  unless (null searchPaths)
    $ outputDocLn $ nest 2 $ pretty ("search paths:" :: Text) <\> unlines (map pretty searchPaths)

showModules = Action $ uses (target_.modules_) (unlines . map (\ (name, (path, _)) -> prettyMName name <> maybe mempty ((space <>) . S.parens . pretty) path) . Map.toList . getGraph) >>= outputDocLn

showTargets = Action $ uses (target_.targets_) (unlines . map prettyMName . toList) >>= outputDocLn


addPath, removePath :: FilePath -> Action

addPath path = Action $ target_.searchPaths_ %= Set.insert path

removePath path = Action $ target_.searchPaths_ %= Set.delete path


addTarget, removeTarget :: [MName] -> Action

addTarget targets = Action $ do
  target_.targets_ %= Set.union (Set.fromList targets)
  target_ `zoom` reloadModules

-- FIXME: remove things depending on it
removeTarget targets = Action $ target_.targets_ %= (Set.\\ Set.fromList targets)


showType, showEval :: S.Ann S.Expr -> Action

showType e = Action $ do
  e ::: _T <- runElab $ Elab.elabSynthTerm (Elab.synth (Elab.synthExpr e))
  opts <- get
  outputDocLn (getPrint (ann (printExpr opts mempty e ::: printType opts mempty _T)))

showEval e = Action $ do
  e' ::: _T <- runElab $ Elab.elabSynthTerm $ locally Elab.sig_ (I.singleton (I.Interface (["Effect", "Console"]:.:U "Output") Nil) :) $ Elab.synth (Elab.synthExpr e)
  e'' <- runElab $ runEvalMain e'
  opts <- get
  outputDocLn (getPrint (ann (printExpr opts mempty e'' ::: printType opts mempty _T)))

runEvalMain :: (Has (Error (Notice.Notice (Doc Style)) :+: Output :+: Reader Graph :+: Reader Module :+: State Options) sig m, MonadFail m) => Expr -> m Expr
runEvalMain e = runEval (E.quoteV 0 =<< runReader mempty (eval e)) pure
  -- where
  -- hdl = [(write, Handler handle)]
  -- write = fromList ["Effect", "Console"] :.: U "write"
  -- handle (FromList [o]) k = do
  --   E.VString s <- o hdl
  --   outputText s *> k unit
  -- handle _              _ = unhandled
  -- unhandled = throwError $ Notice.Notice (Just Notice.Error) [] (fillSep @(Doc Style) [reflow "unhandled effect operator"]) []

showKind :: S.Ann S.Type -> Action
showKind _T = Action $ do
  _T ::: _K <- runElab $ Elab.elabSynthType (Elab.isType (Elab.synthType _T))
  opts <- get
  outputDocLn (getPrint (ann (printType opts mempty _T ::: printKind mempty _K)))


helpDoc :: Doc Style
helpDoc = tabulate2 (stimes (3 :: Int) space) (map entry (getCommands commands))
  where
  entry c =
    ( concatWith (surround (comma <> space)) (map (annotate Style.Command . pretty . (':':)) (symbols c)) <> maybe mempty ((space <>) . enclose (pretty '<') (pretty '>') . pretty) (meta c)
    , w (usage c))
  w = align . fillSep . map pretty . words


prompt :: (Has (Input :+: State REPL) sig m, MonadIO m) => m (Maybe Source)
prompt = do
  line <- gets line
  line_ %= (+ 1)
  fn <- gets promptFunction
  p <- liftIO $ fn line
  fmap (sourceFromString Nothing line) <$> getInputLine p

runElab :: Has (State Options :+: State REPL) sig m => I.WriteC (Notice.Notice (Doc Style)) Elab.Warn (I.ThrowC (Notice.Notice (Doc Style)) Elab.Err (ReaderC MName (ReaderC Module (ReaderC Graph m)))) a -> m a
runElab m = do
  graph <- use (target_.modules_)
  localDefs <- use localDefs_
  opts <- get
  runReader graph . runReader localDefs . runReader ((name :: Module -> MName) localDefs) . rethrowElabErrors opts . rethrowElabWarnings $ m
