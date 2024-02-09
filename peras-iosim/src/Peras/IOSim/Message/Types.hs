{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.Message.Types (
  InEnvelope(..)
, OutMessage(..)
, OutEnvelope(..)
) where

import Control.Applicative ((<|>))
import Control.Monad.Class.MonadTime (UTCTime)
import GHC.Generics (Generic)
import Peras.IOSim.Types (ByteSize)
import Peras.Message (Message, NodeId)
import Peras.Block (Block)
import Peras.Orphans ()

import qualified Data.Aeson as A

data InEnvelope t =
  InEnvelope
  {
    origin :: Maybe NodeId
  , inMessage :: Message t
  }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance A.FromJSON t => A.FromJSON (InEnvelope t) where
  parseJSON =
    A.withObject "InEnvelope"
      $ \o ->
        do
          origin <- o A..: "origin"
          inMessage <-o A..: "inMessage"
          pure InEnvelope{..}

instance A.ToJSON t => A.ToJSON (InEnvelope t) where
  toJSON InEnvelope{..} =
    A.object 
      [
        "origin" A..= origin
      , "inMessage" A..= inMessage
      ]

-- TODO: Refactor (or eliminate) when the Agda and QuickCheck code stabilizes.
data OutMessage t =
    FetchBlock (Block t)
  | SendMessage (Message t)
  deriving stock (Eq, Generic, Ord, Read, Show)

instance A.FromJSON t => A.FromJSON (OutMessage t) where
  parseJSON =
    A.withObject "OutMessage"
      $ \o ->
        do
          output <- o A..: "output"
          case output of
            "NextSlot" -> FetchBlock <$> o A..: "block"
            "SendMessage" -> SendMessage <$> o A..: "message"
            _ -> fail $ "Illegal output: " <> output

instance A.ToJSON t => A.ToJSON (OutMessage t) where
  toJSON (FetchBlock block) =
    A.object
      [
        "output" A..= ("FetchBlock" :: String)
      , "block" A..= block
      ]
  toJSON (SendMessage message) =
    A.object
      [
        "output" A..= ("SendMessage" :: String)
      , "message" A..= message
      ]

data OutEnvelope t =
    OutEnvelope
    {
      timestamp :: UTCTime
    , outMessage :: OutMessage t
    , bytes :: ByteSize
    , destination :: NodeId
    , source :: NodeId
    }
  | Idle
    {
      timestamp :: UTCTime
    , source :: NodeId
    }
    deriving stock (Eq, Generic, Ord, Read, Show)

instance A.FromJSON t => A.FromJSON (OutEnvelope t) where
  parseJSON =
    A.withObject "OutEnvelope"
      $ \o ->
        let
          parseMessage = OutEnvelope <$> o A..: "timestamp" <*> o A..: "outMessage" <*> o A..: "bytes" <*> o A..: "destination" <*> o A..: "source"
          parseIdle = Idle <$> o A..: "timestamp" <*> o A..: "source"
        in
          parseMessage <|> parseIdle
  
instance A.ToJSON t => A.ToJSON (OutEnvelope t) where
  toJSON OutEnvelope{..} =
    A.object
      [
        "timestamp" A..= timestamp
      , "outMessage" A..= outMessage
      , "bytes" A..= bytes
      , "destination" A..= destination
      , "source" A..= source
      ]
  toJSON Idle{..} =
    A.object
      [
        "timestamp" A..= timestamp
      , "source" A..= source
      ]
