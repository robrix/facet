module Facet.CLI
( main
) where

import           Control.Monad (join)
import           Data.Version (showVersion)
import qualified Facet.LSP as LSP
import qualified Facet.REPL as REPL
import qualified Facet.Run as Run
import           Options.Applicative as Options
import qualified Paths_facet as Library (version)
import           System.Exit

main :: IO ()
main = join (execParser argumentsParser) >>= exitWith

argumentsParser :: ParserInfo (IO ExitCode)
argumentsParser = info
  (version <*> helper <*> hsubparser commands)
  (  fullDesc
  <> progDesc "Facet is a language featuring algebraic effects and handlers."
  <> header   "Facet - a functional, effectful language")

-- TODO:
-- - format
-- - build
-- - diff
-- - lint
commands :: Mod CommandFields (IO ExitCode)
commands
  =  command "repl" (info replParser    (progDesc "run the repl"))
  <> command "run"  (info runFileParser (progDesc "run a program"))
  <> command "lsp"  (info lspParser     (progDesc "run an LSP server"))

replParser :: Parser (IO ExitCode)
replParser = pure REPL.repl

runFileParser :: Parser (IO ExitCode)
runFileParser = Run.runFile <$> strArgument (metavar "PATH")

lspParser :: Parser (IO ExitCode)
lspParser = LSP.lsp <$> (Just <$> strOption (long "path" <> metavar "PATH") <|> pure Nothing)

versionString :: String
versionString = "facetc version " <> showVersion Library.version

version :: Options.Parser (a -> a)
version = infoOption versionString (long "version" <> short 'V' <> help "Output version info.")
