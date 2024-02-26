{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.Message.Types (
  InEnvelope (..),
  OutMessage (..),
  OutEnvelope (..),
) where

import Control.Applicative ((<|>))
import Control.Monad.Class.MonadTime (UTCTime)
import GHC.Generics (Generic)
import Peras.Block (Block)
import Peras.IOSim.Node.Types (NodeState)
import Peras.IOSim.Types (ByteSize, Votes)
import Peras.Message (Message, NodeId)
import Peras.Orphans ()

import qualified Data.Aeson as A
import qualified Data.Aeson.Types as A
import Peras.Chain (Chain)

data InEnvelope
  = InEnvelope
      { origin :: Maybe NodeId
      , inMessage :: Message Votes
      }
  | Stop
  deriving stock (Eq, Generic, Ord, Read, Show)

instance A.FromJSON InEnvelope where
  parseJSON =
    A.withObject "InEnvelope" $
      \o ->
        let parseInEnvelope =
              do
                origin <- o A..: "origin"
                inMessage <- o A..: "inMessage"
                pure InEnvelope{..}
            parseStop =
              do
                action <- o A..: "action"
                if action == "Stop"
                  then pure Stop
                  else A.parseFail $ "Illegal action: " <> action
         in parseInEnvelope <|> parseStop

instance A.ToJSON InEnvelope where
  toJSON InEnvelope{..} =
    A.object
      [ "origin" A..= origin
      , "inMessage" A..= inMessage
      ]
  toJSON Stop =
    A.object
      [ "action" A..= ("Stop" :: String)
      ]

-- TODO: Refactor (or eliminate) when the Agda and QuickCheck code stabilizes.
data OutMessage
  = FetchBlock (Block Votes)
  | SendMessage (Message Votes)
  deriving stock (Eq, Generic, Ord, Read, Show)

instance A.FromJSON OutMessage where
  parseJSON =
    A.withObject "OutMessage" $
      \o ->
        do
          output <- o A..: "output"
          case output of
            "NextSlot" -> FetchBlock <$> o A..: "block"
            "SendMessage" -> SendMessage <$> o A..: "message"
            _ -> A.parseFail $ "Illegal output: " <> output

instance A.ToJSON OutMessage where
  toJSON (FetchBlock block) =
    A.object
      [ "output" A..= ("FetchBlock" :: String)
      , "block" A..= block
      ]
  toJSON (SendMessage message) =
    A.object
      [ "output" A..= ("SendMessage" :: String)
      , "message" A..= message
      ]

data OutEnvelope
  = OutEnvelope
      { timestamp :: UTCTime
      , source :: NodeId
      , outMessage :: OutMessage
      , bytes :: ByteSize
      , destination :: NodeId
      }
  | Idle
      { timestamp :: UTCTime
      , source :: NodeId
      , bestChain :: Chain Votes
      }
  | Exit
      { timestamp :: UTCTime
      , source :: NodeId
      , nodeState :: NodeState
      }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance A.FromJSON OutEnvelope where
  parseJSON =
    A.withObject "OutEnvelope" $
      \o ->
        let parseMessage =
              OutEnvelope
                <$> o A..: "timestamp"
                <*> o A..: "source"
                <*> o A..: "outMessage"
                <*> o A..: "bytes"
                <*> o A..: "destination"
            parseIdle = Idle <$> o A..: "timestamp" <*> o A..: "source" <*> o A..: "bestChain"
            parseExit = Exit <$> o A..: "timestamp" <*> o A..: "source" <*> o A..: "nodeState"
         in parseMessage <|> parseIdle <|> parseExit

instance A.ToJSON OutEnvelope where
  toJSON OutEnvelope{..} =
    A.object
      [ "timestamp" A..= timestamp
      , "source" A..= source
      , "outMessage" A..= outMessage
      , "bytes" A..= bytes
      , "destination" A..= destination
      ]
  toJSON Idle{..} =
    A.object
      [ "timestamp" A..= timestamp
      , "source" A..= source
      , "bestChain" A..= bestChain
      ]
  toJSON Exit{..} =
    A.object
      [ "timestamp" A..= timestamp
      , "source" A..= source
      , "nodeState" A..= nodeState
      ]
