{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
module Facet.REPL
( repl
) where

import           Control.Applicative ((<|>))
import           Control.Carrier.Empty.Church
import           Control.Carrier.Error.Church
import           Control.Carrier.Fresh.Church
import           Control.Carrier.Parser.Church
import           Control.Carrier.Readline.Haskeline
import           Control.Carrier.State.Church
import           Control.Effect.Lens (use, (%=))
import           Control.Effect.Parser.Notice (Level(..), Style(..), prettyNoticeWith)
import           Control.Effect.Parser.Source (Source(..))
import           Control.Effect.Parser.Span (Pos(..))
import           Control.Lens (Lens', lens)
import           Control.Monad.IO.Class
import           Data.Char
import           Data.Foldable (for_)
import qualified Data.Map as Map
import           Data.Semigroup
import           Data.Text.Lazy (unpack)
import           Facet.Algebra
import           Facet.Parser
import           Facet.Pretty hiding (renderLazy)
import           Facet.Print
import           Facet.REPL.Parser
import           Facet.Stack
import           Facet.Surface (Expr, Type)
import           Prelude hiding (print)
import           Prettyprinter as P hiding (column, width)
import           Prettyprinter.Render.Terminal (AnsiStyle, Color(..), bold, color, renderLazy)
import           Text.Parser.Char hiding (space)
import           Text.Parser.Combinators
import           Text.Parser.Position
import           Text.Parser.Token hiding (brackets, comma)

repl :: IO ()
repl
  = runReadlineWithHistory
  . evalState REPL{ files = mempty, promptFunction = defaultPromptFunction }
  . evalEmpty
  . evalFresh 0
  $ loop

defaultPromptFunction :: Int -> IO String
defaultPromptFunction _ = pure $ "\ESC]0;facet\x7" <> cyan <> "λ " <> plain
  where
  cyan = "\ESC[1;36m\STX"
  plain = "\ESC[0m\STX"


data REPL = REPL
  { files          :: Map.Map FilePath File
  , promptFunction :: Int -> IO String
  }

data File = File
  { loaded :: Bool
  }

files_ :: Lens' REPL (Map.Map FilePath File)
files_ = lens files (\ r files -> r{ files })

loop :: (Has Empty sig m, Has Fresh sig m, Has Readline sig m, Has (State REPL) sig m, MonadIO m) => m ()
loop = do
  (line, resp) <- prompt
  runError (print . prettyNoticeWith ansiStyle . uncurry errToNotice) pure $ case resp of
    -- FIXME: evaluate expressions
    Just resp -> runParserWithString (Pos line 0) resp (runFacet [] (whole commandParser)) >>= runAction
    Nothing   -> pure ()
  loop
  where
  commandParser = parseCommands commands

  runAction = \case
    Help -> print helpDoc
    Quit -> empty
    Load path -> load path
    Reload -> reload
    Type e -> print (getPrint (foldSExpr surface Nil e)) -- FIXME: elaborate the expr & show the type
    Kind t -> print (getPrint (foldSType surface Nil t)) -- FIXME: elaborate the type & show the kind


-- TODO:
-- - multiline
commands :: [Command Action]
commands =
  [ Command ["help", "h", "?"]  "display this list of commands" $ Pure Help
  , Command ["quit", "q"]       "exit the repl"                 $ Pure Quit
  , Command ["load", "l"]       "add a module to the repl"      $ Meta "path" load_
  , Command ["reload", "r", ""] "reload the loaded modules"     $ Pure Reload
  , Command ["type", "t"]       "show the type of <expr>"       $ Meta "expr" type_
  , Command ["kind", "k"]       "show the kind of <type>"       $ Meta "type" kind_
  ]

load_ :: PositionParsing p => p Action

load_ = Load <$> (stringLiteral <|> some (satisfy (not . isSpace)))

type_, kind_ :: (PositionParsing p, Monad p) => p Action

type_ = Type <$> runFacet [] (whole expr )
kind_ = Kind <$> runFacet [] (whole type')


data Action
  = Help
  | Quit
  | Load FilePath
  | Reload
  | Type (Spanned Expr)
  | Kind (Spanned Type)

load :: (Has (Error (Source, Err)) sig m, Has Readline sig m, Has (State REPL) sig m, MonadIO m) => FilePath -> m ()
load path = do
  files_ %= Map.insert path File{ loaded = False }
  runParserWithFile path (runFacet [] (whole module')) >>= print . getPrint . foldSModule surface

reload :: (Has (Error (Source, Err)) sig m, Has Readline sig m, Has (State REPL) sig m, MonadIO m) => m ()
reload = do
  files <- use files_
  -- FIXME: topological sort
  let ln = length files
  for_ (zip [(1 :: Int)..] (Map.keys files)) $ \ (i, path) -> do
    -- FIXME: module name
    print $ annotate (color Green) (brackets (pretty i <+> pretty "of" <+> pretty ln)) <+> nest 2 (group (fillSep [ pretty "Loading", pretty path ]))
    (runParserWithFile path (runFacet [] (whole module')) >>= print . getPrint . foldSModule surface) `catchError` \ n -> print (indent 2 (prettyNoticeWith ansiStyle (uncurry errToNotice n)))

helpDoc :: Doc AnsiStyle
helpDoc = tabulate2 (stimes (3 :: Int) P.space) entries
  where
  entries = map entry commands
  entry c = (concatWith (surround (comma <> space)) (map (pretty . (':':)) (symbols c)) <> maybe mempty ((space <>) . enclose (pretty '<') (pretty '>') . pretty) (meta c), w (usage c))
  w = align . fillSep . map pretty . words


prompt :: (Has Fresh sig m, Has Readline sig m, Has (State REPL) sig m, MonadIO m) => m (Int, Maybe String)
prompt = do
  line <- fresh
  fn <- gets promptFunction
  p <- liftIO $ fn line
  (,) line <$> getInputLine p

print :: (Has Readline sig m, MonadIO m) => Doc AnsiStyle -> m ()
print d = do
  opts <- liftIO layoutOptionsForTerminal
  outputStrLn (unpack (renderLazy (layoutSmart opts d)))


ansiStyle :: Style AnsiStyle
ansiStyle = Style
  { pathStyle   = annotate bold
  , levelStyle  = \case
    Warn  -> annotate (color Magenta)
    Error -> annotate (color Red)
  , posStyle    = annotate bold
  , gutterStyle = annotate (color Blue)
  , eofStyle    = annotate (color Blue)
  , caretStyle  = annotate (color Green)
  }
