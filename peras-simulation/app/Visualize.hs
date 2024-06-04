{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

import qualified Data.Aeson as A
import qualified Data.ByteString.Lazy.Char8 as LBS8
import Data.Version (showVersion)
import Paths_peras_simulation (version)
import Peras.Abstract.Protocol.Visualizer (visualize, writeGraph)
import System.Exit (die)

import qualified Options.Applicative as O

main :: IO ()
main =
  do
    Command{..} <- O.execParser commandParser
    mapM A.eitherDecode' . LBS8.lines <$> LBS8.readFile traceFile
      >>= \case
        Left e -> die $ show e
        Right events ->
          whenJust dotFile $
            flip writeGraph $
              visualize events

whenJust ::
  Applicative m =>
  Maybe a ->
  (a -> m ()) ->
  m ()
whenJust = flip . maybe $ pure ()

data Command = Command
  { traceFile :: FilePath
  , dotFile :: Maybe FilePath
  }
  deriving stock (Eq, Ord, Read, Show)

commandParser :: O.ParserInfo Command
commandParser =
  let commandOptions =
        Command
          <$> O.strOption
            (O.long "trace-file" <> O.metavar "FILE" <> O.help "Path to input JSON-array file containing simulation trace.")
          <*> (O.optional . O.strOption)
            (O.long "dot-file" <> O.metavar "FILE" <> O.help "Path to output GraphViz DOT file containing visualization.")
   in O.info
        ( O.helper
            <*> O.infoOption ("peras-visualize " <> showVersion version) (O.long "version" <> O.help "Show version.")
            <*> commandOptions
        )
        ( O.fullDesc
            <> O.progDesc "This command-line tool visualizes Peras simulation traces."
            <> O.header "peras-visualize: visualize Peras simulation traces"
        )
