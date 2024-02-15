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
import Peras.IOSim.Types (ByteSize)
import Peras.Message (Message, NodeId)
import Peras.Orphans ()

import qualified Data.Aeson as A
import qualified Data.Aeson.Types as A

data InEnvelope v
  = InEnvelope
      { origin :: Maybe NodeId
      , inMessage :: Message v
      }
  | Stop
  deriving stock (Eq, Generic, Ord, Read, Show)

instance A.FromJSON v => A.FromJSON (InEnvelope v) where
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

instance A.ToJSON v => A.ToJSON (InEnvelope v) where
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
data OutMessage v
  = FetchBlock (Block v)
  | SendMessage (Message v)
  deriving stock (Eq, Generic, Ord, Read, Show)

instance A.FromJSON v => A.FromJSON (OutMessage v) where
  parseJSON =
    A.withObject "OutMessage" $
      \o ->
        do
          output <- o A..: "output"
          case output of
            "NextSlot" -> FetchBlock <$> o A..: "block"
            "SendMessage" -> SendMessage <$> o A..: "message"
            _ -> A.parseFail $ "Illegal output: " <> output

instance A.ToJSON v => A.ToJSON (OutMessage v) where
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

data OutEnvelope v
  = OutEnvelope
      { timestamp :: UTCTime
      , source :: NodeId
      , outMessage :: OutMessage v
      , bytes :: ByteSize
      , destination :: NodeId
      }
  | Idle
      { timestamp :: UTCTime
      , source :: NodeId
      , currentState :: NodeState v
      }
  | Exit
      { timestamp :: UTCTime
      , source :: NodeId
      , nodeState :: NodeState v
      }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance A.FromJSON v => A.FromJSON (OutEnvelope v) where
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
            parseIdle = Idle <$> o A..: "timestamp" <*> o A..: "source" <*> o A..: "currentState"
            parseExit = Exit <$> o A..: "timestamp" <*> o A..: "source" <*> o A..: "nodeState"
         in parseMessage <|> parseIdle <|> parseExit

instance A.ToJSON v => A.ToJSON (OutEnvelope v) where
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
      , "currentState" A..= currentState
      ]
  toJSON Exit{..} =
    A.object
      [ "timestamp" A..= timestamp
      , "source" A..= source
      , "nodeState" A..= nodeState
      ]
