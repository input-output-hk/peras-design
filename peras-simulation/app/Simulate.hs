{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

import Control.Concurrent.Class.MonadSTM (newTVarIO)
import qualified Data.Aeson as A
import qualified Data.ByteString.Lazy.Char8 as LBS8
import Data.Default (def)
import Data.Version (showVersion)
import Paths_peras_simulation (version)
import Peras.Prototype.Environment (mkSimpleScenario)
import Peras.Prototype.Network (simulate, simulateNetwork)
import Peras.Prototype.Trace (perasTracer)
import Peras.Prototype.Visualizer (makeVisTracer)
import System.Exit (die)

import qualified Data.Yaml as Y
import qualified Options.Applicative as O

singleMain :: IO ()
singleMain = mkSimpleScenario >>= simulateNetwork perasTracer >>= print

multinodeMain :: FilePath -> Maybe FilePath -> Maybe FilePath -> IO ()
multinodeMain inputFile outputFile logFile =
  do
    input <- either (die . show) pure =<< Y.decodeFileEither inputFile
    (tracer, reader) <- makeVisTracer
    controlVar <- newTVarIO def
    simulate tracer controlVar input
      >>= \case
        Left e -> die $ show e
        Right output -> do
          whenJust outputFile $
            flip A.encodeFile output
          whenJust logFile $
            \file -> do
              events <- reader
              LBS8.writeFile file . LBS8.unlines $ A.encode <$> events

main :: IO ()
main =
  do
    Command{..} <- O.execParser commandParser
    case inFile of
      Nothing -> singleMain -- FIXME: Make this a subcommand.
      Just inFile' -> multinodeMain inFile' outFile traceFile

whenJust ::
  Applicative m =>
  Maybe a ->
  (a -> m ()) ->
  m ()
whenJust = flip . maybe $ pure ()

data Command = Command
  { inFile :: Maybe FilePath
  , outFile :: Maybe FilePath
  , traceFile :: Maybe FilePath
  }
  deriving stock (Eq, Ord, Read, Show)

commandParser :: O.ParserInfo Command
commandParser =
  let commandOptions =
        Command
          <$> (O.optional . O.strOption)
            (O.long "in-file" <> O.metavar "FILE" <> O.help "Path to input YAML file containing initial simulation configuration.")
          <*> (O.optional . O.strOption)
            (O.long "out-file" <> O.metavar "FILE" <> O.help "Path to output YAML file containing final simulation configuration.")
          <*> (O.optional . O.strOption)
            (O.long "trace-file" <> O.metavar "FILE" <> O.help "Path to output JSON-array file containing simulation trace.")
   in O.info
        ( O.helper
            <*> O.infoOption ("peras-simulate " <> showVersion version) (O.long "version" <> O.help "Show version.")
            <*> commandOptions
        )
        ( O.fullDesc
            <> O.progDesc "This command-line tool simulates the Peras protocol."
            <> O.header "peras-simulate: simulate Peras protocol"
        )
