{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE RecordWildCards #-}

module Main (
  main,
) where

import Control.Monad (void)
import Data.Maybe (fromJust, isJust)
import Data.Version (showVersion)
import Paths_peras_iosim (version)
import Peras.IOSim.GraphViz (chainGraph, peersGraph, writeGraph)
import Peras.IOSim.Simulate (simulate, writeReport, writeTrace)
import System.Directory (removeFile)
import System.Exit (die)
import System.IO.Temp (emptySystemTempFile)
import System.Process (system)

import qualified Data.Yaml as Y
import qualified Options.Applicative as O

main :: IO ()
main =
  do
    Command{..} <- O.execParser commandParser
    parameters <- either (error . show) id <$> Y.decodeFileEither parameterFile
    protocol <- either (error . show) id <$> Y.decodeFileEither protocolFile
    let (result, trace) = simulate parameters protocol $ isJust traceFile
    whenJust traceFile $
      flip writeTrace $
        fromJust trace
    case result of
      Right state ->
        do
          whenJust resultFile $
            flip writeReport state
          let peers = peersGraph state
          whenJust networkDotFile $
            flip writeGraph peers
          whenJust networkPngFile $
            \pngFile ->
              do
                dotFile <- emptySystemTempFile "network.dot"
                writeGraph dotFile peers -- FIXME: Potentially duplicative.
                void . system $ "circo -Tpng -o " <> pngFile <> " " <> dotFile
                removeFile dotFile
          let chains = chainGraph state
          whenJust chainDotFile $
            flip writeGraph chains
          whenJust chainPngFile $
            \pngFile ->
              do
                dotFile <- emptySystemTempFile "chain.dot"
                writeGraph dotFile chains -- FIXME: Potentially duplicative.
                void . system $ "dot -Tpng -o " <> pngFile <> " " <> dotFile
                removeFile dotFile
      Left failure -> die $ show failure

whenJust ::
  Applicative m =>
  Maybe a ->
  (a -> m ()) ->
  m ()
whenJust = flip . maybe $ pure ()

data Command = Command
  { parameterFile :: FilePath
  , protocolFile :: FilePath
  , traceFile :: Maybe FilePath
  , resultFile :: Maybe FilePath
  , networkDotFile :: Maybe FilePath
  , networkPngFile :: Maybe FilePath
  , chainDotFile :: Maybe FilePath
  , chainPngFile :: Maybe FilePath
  }
  deriving stock (Eq, Ord, Read, Show)

commandParser :: O.ParserInfo Command
commandParser =
  let commandOptions =
        Command
          <$> O.strOption (O.long "parameter-file" <> O.metavar "FILE" <> O.help "Path to YAML file with simulation parameters.")
          <*> O.strOption (O.long "protocol-file" <> O.metavar "FILE" <> O.help "Path to YAML file with protocol parameters.")
          <*> (O.optional . O.strOption)
            (O.long "trace-file" <> O.metavar "FILE" <> O.help "Path to output text file for simulation trace.")
          <*> (O.optional . O.strOption)
            (O.long "result-file" <> O.metavar "FILE" <> O.help "Path to output JSON file for simulation results.")
          <*> (O.optional . O.strOption)
            (O.long "network-dot-file" <> O.metavar "FILE" <> O.help "Path to output GraphViz .dot file of network visualizaton.")
          <*> (O.optional . O.strOption)
            ( O.long "network-png-file"
                <> O.metavar "FILE"
                <> O.help "Path to output PNG file of network visualizaton. Requires `GraphViz` executable."
            )
          <*> (O.optional . O.strOption)
            (O.long "chain-dot-file" <> O.metavar "FILE" <> O.help "Path to output GraphViz .dot file of chain visualizaton.")
          <*> (O.optional . O.strOption)
            ( O.long "chain-png-file"
                <> O.metavar "FILE"
                <> O.help "Path to output PNG file of chain visualizaton. Requires `GraphViz` executable."
            )
   in O.info
        ( O.helper
            <*> (O.infoOption ("peras-iosim " <> showVersion version) $ O.long "version" <> O.help "Show version.")
            <*> commandOptions
        )
        ( O.fullDesc
            <> O.progDesc "This command-line tool simulates and visualizes Peras protocol simulations."
            <> O.header "peras-iosim: simulate Peras protocol"
        )
