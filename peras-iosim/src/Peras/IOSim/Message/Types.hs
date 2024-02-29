{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

module Peras.IOSim.Message.Types (
  InEnvelope (..),
  OutMessage (..),
  OutEnvelope (..),
) where

import Control.Monad.Class.MonadTime (UTCTime)
import Data.Aeson (FromJSON, ToJSON)
import GHC.Generics (Generic)
import Peras.Block (Block)
import Peras.Chain (Chain)
import Peras.IOSim.Node.Types (NodeState)
import Peras.IOSim.Types (ByteSize, Message')
import Peras.Message (NodeId)
import Peras.Orphans ()

data InEnvelope
  = InEnvelope
      { origin :: Maybe NodeId
      , inMessage :: Message'
      }
  | Stop
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON InEnvelope
instance ToJSON InEnvelope

-- TODO: Refactor (or eliminate) when the Agda and QuickCheck code stabilizes.
data OutMessage
  = FetchBlock Block
  | SendMessage Message'
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON OutMessage
instance ToJSON OutMessage

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
      , bestChain :: Chain
      }
  | Exit
      { timestamp :: UTCTime
      , source :: NodeId
      , nodeState :: NodeState
      }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON OutEnvelope
instance ToJSON OutEnvelope
