module Facet.REPL
( repl
) where

import           Control.Applicative ((<|>))
import           Control.Carrier.Empty.Church
import           Control.Carrier.Error.Church
import           Control.Carrier.Fresh.Church
import           Control.Carrier.Reader
import           Control.Carrier.Readline.Haskeline
import           Control.Carrier.State.Church
import           Control.Effect.Lens (use, (%=), (.=), (?=))
import           Control.Lens (Getting, Lens', at, itraverse_, ix, lens)
import           Control.Monad (unless)
import           Control.Monad.IO.Class
import           Data.Char
import           Data.Colour.RGBSpace.HSL (hsl)
import           Data.Foldable (toList)
import qualified Data.Map as Map
import           Data.Semigroup (stimes)
import qualified Data.Set as Set
import           Data.Text (pack)
import           Data.Text.Lazy (unpack)
import           Facet.Algebra hiding (Algebra)
import           Facet.Carrier.Parser.Church
import qualified Facet.Carrier.State.Lens as L
import qualified Facet.Carrier.Throw.Inject as I
import           Facet.Core
import qualified Facet.Elab as Elab
import qualified Facet.Env as Env
import           Facet.Eval
import           Facet.Name hiding (Meta, use)
import qualified Facet.Notice as Notice
import           Facet.Notice.Elab
import           Facet.Notice.Parser
import           Facet.Parser
import           Facet.Pretty
import           Facet.Print as Print hiding (Type)
import           Facet.REPL.Parser
import           Facet.Source (Source(..), readSourceFromFile, sourceFromString)
import           Facet.Span (Span)
import           Facet.Stack
import           Facet.Style as Style
import           Facet.Surface (Ann, Expr)
import qualified Facet.Surface as Surface
import           Facet.Syntax
import           Prelude hiding (print, span, unlines)
import           Prettyprinter (reAnnotate, reAnnotateS)
import           Silkscreen hiding (Ann, line)
import           System.Console.ANSI
import           System.Directory
import           System.IO.Error
import           Text.Parser.Char hiding (space)
import           Text.Parser.Combinators
import           Text.Parser.Token hiding (brackets, comma)

repl :: IO ()
repl
  = runReadlineWithHistory
  . evalState defaultREPLState
  . evalEmpty
  $ loop


data REPL = REPL
  { line           :: Int
  , files          :: Map.Map FilePath File
  , promptFunction :: Int -> IO String
  , env            :: Env.Env
  , targets        :: [Either FilePath MName]
  -- FIXME: break this down by file/module/whatever so we can load multiple packages
  , searchPaths    :: Set.Set FilePath
  }

line_ :: Lens' REPL Int
line_ = lens line (\ r line -> r{ line })

files_ :: Lens' REPL (Map.Map FilePath File)
files_ = lens files (\ r files -> r{ files })

env_ :: Lens' REPL Env.Env
env_ = lens env (\ r env -> r{ env })

searchPaths_ :: Lens' REPL (Set.Set FilePath)
searchPaths_ = lens searchPaths (\ r searchPaths -> r{ searchPaths })

defaultREPLState :: REPL
defaultREPLState = REPL
  { line           = 0
  , files          = mempty
  , promptFunction = defaultPromptFunction
  , env            = toEnv kernel
  , targets        = []
  , searchPaths    = Set.singleton "src"
  }

defaultPromptFunction :: Int -> IO String
defaultPromptFunction _ = pure $ setTitleCode "facet" <> cyan <> "λ " <> plain
  where
  cyan = setSGRCode [setRGB (hsl 180 1 0.5)]
  plain = setSGRCode []


kernel :: Module
kernel = Module kernelName []
  [ (kernelName :.: T (UName (pack "Type")), DTerm VType ::: VType)
  ]
  where
  kernelName = MName (pack "Kernel")

toEnv :: Module -> Env.Env
toEnv (Module _ _ defs) = Env.fromList $ do
  (mname:.:dname, def ::: _T) <- defs
  case def of
    DTerm v  -> [ (dname, mname :=: Just v ::: _T) ]
    DData cs -> [ (C n,   mname :=: Just v ::: _T) | n :=: v ::: _T <- cs ]


data File = File
  { source :: Maybe Source
  , parsed :: Maybe (Ann Surface.Module)
  , elabed :: Maybe Module
  }

source_ :: Lens' File (Maybe Source)
source_ = lens source (\ f source -> f{ source })

parsed_ :: Lens' File (Maybe (Ann Surface.Module))
parsed_ = lens parsed (\ f parsed -> f{ parsed })

elabed_ :: Lens' File (Maybe Module)
elabed_ = lens elabed (\ f elabed -> f{ elabed })

loaded :: File -> Bool
loaded = \case
  File{ parsed = Just _ } -> True
  _                       -> False

upToDate :: Source -> File -> Bool
upToDate s = \case
  File{ source = Just s'
      , parsed = Just _
      , elabed = Just _
      }                  -> s == s'
  _                      -> False


loop :: (Has Empty sig m, Has Readline sig m, Has (State REPL) sig m, MonadIO m) => m ()
loop = do
  resp <- prompt
  runError (print . prettyNotice') pure $ case resp of
    Just src -> rethrowParseErrors @Style (runParserWithSource src commandParser) >>= runAction src
    Nothing  -> pure ()
  loop
  where
  commandParser = runFacet [] [] (whole (parseCommands commands <|> Eval <$> expr))

  runAction src = \case
    Help -> print helpDoc
    Quit -> empty
    Show t -> case t of
      ShowPaths   -> do
        dir <- liftIO getCurrentDirectory
        print $ nest 2 $ reflow "current working directory:" </> pretty dir
        searchPaths <- gets (toList . searchPaths)
        unless (null searchPaths)
          $ print $ nest 2 $ pretty "search paths:" <\> unlines (map pretty searchPaths)
      -- FIXME: show module names
      ShowModules -> gets (unlines . map pretty . Map.keys . files) >>= print
    Add ModPath path -> searchPaths_ %= Set.insert path
    Add ModTarget path -> load src path
    Remove ModPath path -> searchPaths_ %= Set.delete path
    -- FIXME: remove things depending on it
    Remove ModTarget path -> files_.at path .= Nothing
    Reload -> reload src
    Type e -> do
      _ ::: _T <- elab src $ Elab.elabWith (\ s (e ::: _T) -> (:::) <$> Elab.apply s e <*> Elab.apply s _T) (Elab.elabExpr e Nothing)
      print (prettyCode (ann (foldSExpr surface Nil e ::: foldCValue surface Nil (generalize _T))))
    Kind t -> do
      _ ::: _T <- elab src $ Elab.elabWith (\ s (t ::: _T) -> (:::) <$> Elab.apply s t <*> Elab.apply s _T) (Elab.elabExpr t Nothing)
      print (prettyCode (ann (foldSExpr surface Nil t ::: foldCValue surface Nil (generalize _T))))
    Eval e -> do -- FIXME: actually evaluate
      e' ::: _T <- elab src $ Elab.elabWith (\ s (e ::: _T) -> (:::) <$> Elab.apply s e <*> Elab.apply s _T) (Elab.elabExpr e Nothing)
      e'' <- L.runState env_ $ Env.runEnv $ eval e'
      print (prettyCode (ann (foldCValue surface Nil e'' ::: foldCValue surface Nil _T)))


-- TODO:
-- - multiline
commands :: [Command Action]
commands =
  [ Command ["help", "h", "?"]  "display this list of commands"      $ Pure Help
  , Command ["quit", "q"]       "exit the repl"                      $ Pure Quit
  , Command ["show"]            "show compiler state"                $ Meta "field" $ Show <$> choice
    [ ShowPaths <$ token (string "paths")
    , ShowModules <$ token (string "modules")
    ]
  , Command ["add"]             "add a module/path to the repl"      $ Meta "path" $ choice
    [ Add ModPath <$ token (string "path") <*> path'
    , Add ModTarget <$ token (string "target") <*> path'
    ]
  , Command ["remove", "rm"]    "remove a module/path from the repl" $ Meta "path" $ choice
    [ Remove ModPath <$ token (string "path") <*> path'
    , Remove ModTarget <$ token (string "target") <*> path'
    ]
  , Command ["reload", "r", ""] "reload the loaded modules"          $ Pure Reload
  , Command ["type", "t"]       "show the type of <expr>"            $ Meta "expr" type_
  , Command ["kind", "k"]       "show the kind of <type>"            $ Meta "type" kind_
  ]

path' :: TokenParsing p => p FilePath
path' = stringLiteral <|> some (satisfy (not . isSpace))

type_, kind_ :: (Has Parser sig p, TokenParsing p) => p Action

type_ = Type <$> runFacet [] [] (whole expr)
kind_ = Kind <$> runFacet [] [] (whole type')


data Action
  = Help
  | Quit
  | Show ShowField
  | Add ModField FilePath
  | Remove ModField FilePath
  | Reload
  | Type (Ann Expr)
  | Kind (Ann Expr)
  | Eval (Ann Expr)

data ShowField
  = ShowPaths
  | ShowModules

data ModField
  = ModPath
  | ModTarget

load :: (Has (Error (Notice.Notice Style)) sig m, Has Readline sig m, Has (State REPL) sig m, MonadIO m) => Source -> FilePath -> m ()
load src path = do
  files_ %= Map.insert path File{ source = Nothing, parsed = Nothing, elabed = Nothing }
  reload src

reload :: (Has (Error (Notice.Notice Style)) sig m, Has Readline sig m, Has (State REPL) sig m, MonadIO m) => Source -> m ()
reload src = do
  -- FIXME: order with a topological sort on imports, once those exist
  evalFresh 1 $ files_ ~> \ files -> itraverse_ (reloadFile (length files)) files
  files <- use files_
  let lnAll = length files
      lnLoaded = length (filter loaded (toList files))
      style = if lnLoaded == lnAll then Success else Failure
  print $ fillSep [annotate style (fillSep [pretty lnLoaded, pretty "of", pretty lnAll]), plural (pretty "file") (pretty "files") lnLoaded, pretty "loaded."]
  where
  reloadFile ln path file = handleError (\ n -> print (indent 2 (prettyNotice' n))) $ do
    src <- rethrowIOErrors src $ readSourceFromFile path
    unless (upToDate src file) $ do
      files_.ix path.source_ ?= src

      i <- fresh
      -- FIXME: print the module name
      print $ annotate Progress (brackets (pretty i <+> pretty "of" <+> pretty ln)) <+> nest 2 (group (fillSep [ pretty "Loading", pretty path ]))

      m <- rethrowParseErrors @Style (runParserWithSource src (runFacet [] [] (whole module')))
      files_.ix path.parsed_ ?= m
      (env, m') <- elab src $ Elab.elabModule m
      files_.ix path.elabed_ ?= m'
      env_ %= (<> env)


helpDoc :: Doc Style
helpDoc = tabulate2 (stimes (3 :: Int) space) (map entry commands)
  where
  entry c =
    ( concatWith (surround (comma <> space)) (map (pretty . (':':)) (symbols c)) <> maybe mempty ((space <>) . enclose (pretty '<') (pretty '>') . pretty) (meta c)
    , w (usage c))
  w = align . fillSep . map pretty . words


prompt :: (Has Readline sig m, Has (State REPL) sig m, MonadIO m) => m (Maybe Source)
prompt = do
  line <- gets line
  line_ %= (+ 1)
  fn <- gets promptFunction
  p <- liftIO $ fn line
  fmap (sourceFromString Nothing line) <$> getInputLine p

print :: (Has Readline sig m, MonadIO m) => Doc Style -> m ()
print d = do
  opts <- liftIO layoutOptionsForTerminal
  outputStrLn (unpack (renderLazy (reAnnotateS terminalStyle (layoutSmart opts d))))

prettyNotice' :: Notice.Notice Style -> Doc Style
prettyNotice' = reAnnotate Style.Notice . Notice.prettyNotice

prettyCode :: Print -> Doc Style
prettyCode = reAnnotate Code . getPrint

elab :: Source -> I.ThrowC (Notice.Notice Style) Elab.Err (L.StateC REPL Env.Env (ReaderC Span m)) a -> m a
elab src = runReader (span src) . L.runState env_ . rethrowElabErrors src Code


-- | Compose a getter onto the input of a Kleisli arrow and run it on the 'State'.
(~>) :: Has (State s) sig m => Getting a s a -> (a -> m b) -> m b
lens ~> act = use lens >>= act

infixr 2 ~>


rethrowIOErrors :: (Has (Throw (Notice.Notice Style)) sig m, MonadIO m) => Source -> IO a -> m a
rethrowIOErrors src m = liftIO (tryIOError m) >>= either (throwError . ioErrorToNotice src) pure

ioErrorToNotice :: Source -> IOError -> Notice.Notice Style
ioErrorToNotice src err = Notice.Notice (Just Notice.Error) src (group (reflow (show err))) []

unlines :: Printer p => [p] -> p
unlines = concatWith (<\>)

(<\>) :: Printer p => p -> p -> p
(<\>) = surround hardline

handleError :: Has (Catch e) sig m => (e -> m a) -> m a -> m a
handleError h m = catchError m h
