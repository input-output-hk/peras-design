{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

import qualified Data.Aeson as A
import qualified Data.ByteString.Lazy.Char8 as LBS8
import Data.Version (showVersion)
import Paths_peras_simulation (version)
import Peras.Abstract.Protocol.Environment (mkSimpleScenario)
import Peras.Abstract.Protocol.Network (simulate, simulateNetwork)
import Peras.Abstract.Protocol.Trace (perasTracer)
import Peras.Abstract.Protocol.Visualizer (makeVisTracer, visualize, writeGraph)
import System.Exit (die)

import qualified Data.Yaml as Y
import qualified Options.Applicative as O

-- FIXME: Make this a subcommand.
singleMain :: IO ()
singleMain = mkSimpleScenario >>= simulateNetwork perasTracer >>= print

multinodeMain :: FilePath -> Maybe FilePath -> Maybe FilePath -> Maybe FilePath -> IO ()
multinodeMain inputFile outputFile logFile visFile =
  do
    input <- either (die . show) pure =<< Y.decodeFileEither inputFile
    (tracer, reader) <- makeVisTracer
    simulate tracer input
      >>= \case
        Left e -> die $ show e
        Right output -> do
          whenJust outputFile $
            flip Y.encodeFile output
          events <- reader
          whenJust logFile $
            flip LBS8.writeFile $
              LBS8.unlines $
                A.encode <$> events
          whenJust visFile $
            flip writeGraph $
              visualize events

main :: IO ()
main =
  do
    Command{..} <- O.execParser commandParser
    case inFile of
      Nothing -> singleMain
      Just inFile' -> multinodeMain inFile' outFile traceFile dotFile

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
  , dotFile :: Maybe FilePath
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
          <*> (O.optional . O.strOption)
            (O.long "dot-file" <> O.metavar "FILE" <> O.help "Path to output GraphViz DOT file containing visualiization.")
   in O.info
        ( O.helper
            <*> O.infoOption ("peras-iosim " <> showVersion version) (O.long "version" <> O.help "Show version.")
            <*> commandOptions
        )
        ( O.fullDesc
            <> O.progDesc "This command-line tool simulates the Peras protocol."
            <> O.header "peras-simulate: simulate Peras protocol"
        )
