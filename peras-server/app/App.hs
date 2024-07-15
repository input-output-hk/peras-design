{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

module Main where

import Control.Concurrent.Class.MonadSTM.TVar (newTVarIO)
import Data.Aeson (FromJSON, ToJSON)
import qualified Data.Aeson as A (encode, encodeFile)
import qualified Data.ByteString.Lazy.Char8 as LBS8 (unlines, writeFile)
import Data.Default (def)
import Data.Version (showVersion)
import qualified Data.Yaml as Y (decodeFileEither)
import GHC.Generics (Generic)
import qualified Options.Applicative as O
import Paths_peras_server (version)
import Peras.Prototype.Network (SimControl (delay), simulate)
import Peras.Prototype.Network.Arbitrary (genSimConfigIO)
import Peras.Prototype.Types (PerasParams (..))
import Peras.Prototype.Visualizer (makeVisTracer)
import System.Exit (die)

data AppControl = Simulate
  { duration :: Integer
  , parties :: Integer
  , u :: Integer
  , a :: Integer
  , r :: Integer
  , k :: Integer
  , l :: Integer
  , tau :: Integer
  , b :: Integer
  , committee :: Integer
  , delta :: Integer
  , activeSlots :: Double
  , rngSeed :: Int
  }
  deriving (Eq, Generic, Show)

instance FromJSON AppControl
instance ToJSON AppControl

main :: IO ()
main =
  do
    Command{..} <- O.execParser commandParser
    Simulate{..} <- either (die . show) pure =<< Y.decodeFileEither inFile
    (tracer, reader) <- makeVisTracer
    controlVar <- newTVarIO $ def{delay = 0}
    simConfig <-
      genSimConfigIO
        def{perasU = u, perasA = a, perasR = r, perasK = k, perasL = l, perasτ = tau, perasB = b, perasΔ = delta}
        activeSlots
        parties
        committee
        (fromIntegral duration)
        rngSeed
    simulate tracer controlVar simConfig
      >>= \case
        Left e -> die $ show e
        Right output -> do
          whenJust outFile $
            flip A.encodeFile output
          whenJust traceFile $
            \file -> do
              events <- reader
              LBS8.writeFile file . LBS8.unlines $ A.encode <$> events

whenJust ::
  Applicative m =>
  Maybe a ->
  (a -> m ()) ->
  m ()
whenJust = flip . maybe $ pure ()

data Command = Command
  { inFile :: FilePath
  , outFile :: Maybe FilePath
  , traceFile :: Maybe FilePath
  }
  deriving (Eq, Ord, Read, Show)

commandParser :: O.ParserInfo Command
commandParser =
  let commandOptions =
        Command
          <$> O.strOption
            (O.long "in-file" <> O.metavar "FILE" <> O.help "Path to input YAML file containing initial simulation configuration.")
          <*> (O.optional . O.strOption)
            (O.long "out-file" <> O.metavar "FILE" <> O.help "Path to output YAML file containing final simulation configuration.")
          <*> (O.optional . O.strOption)
            (O.long "trace-file" <> O.metavar "FILE" <> O.help "Path to output JSON-array file containing simulation trace.")
   in O.info
        ( O.helper
            <*> O.infoOption ("peras-app " <> showVersion version) (O.long "version" <> O.help "Show version.")
            <*> commandOptions
        )
        ( O.fullDesc
            <> O.progDesc "This command-line tool simulates the Peras protocol."
            <> O.header "peras-app: simulate Peras protocol"
        )
