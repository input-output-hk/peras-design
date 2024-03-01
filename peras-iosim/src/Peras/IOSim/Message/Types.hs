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
import Generic.Random (genericArbitrary, uniform)
import Peras.Arbitraries ()
import Peras.Block (Block)
import Peras.Chain (Chain)
import Peras.IOSim.Node.Types (NodeState)
import Peras.IOSim.Types (ByteSize, Message')
import Peras.Message (NodeId)
import Peras.Orphans ()
import Test.QuickCheck (Arbitrary (..), frequency)
import Test.QuickCheck.Instances.Time ()

data InEnvelope
  = InEnvelope
      { origin :: Maybe NodeId
      , inMessage :: Message'
      }
  | Stop
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON InEnvelope
instance ToJSON InEnvelope

instance Arbitrary InEnvelope where
  arbitrary =
    frequency
      [ (9, InEnvelope <$> arbitrary <*> arbitrary)
      , (1, pure Stop)
      ]

-- TODO: Refactor (or eliminate) when the Agda and QuickCheck code stabilizes.
data OutMessage
  = FetchBlock Block
  | SendMessage Message'
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON OutMessage
instance ToJSON OutMessage

instance Arbitrary OutMessage where
  arbitrary = genericArbitrary uniform

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

instance Arbitrary OutEnvelope where
  arbitrary = genericArbitrary uniform
