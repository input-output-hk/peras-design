{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

module Peras.IOSim.Message.Types (
  InEnvelope (..),
  OutEnvelope (..),
  mkUniqueId,
) where

import Control.Monad.Class.MonadTime (UTCTime)
import Data.Aeson (FromJSON, ToJSON)
import Data.Hashable (Hashable, hash)
import GHC.Generics (Generic)
import Generic.Random (genericArbitrary, uniform)
import Peras.Arbitraries ()
import Peras.Chain (Chain)
import Peras.Event (UniqueId (..))
import Peras.IOSim.Node.Types (NodeState)
import Peras.IOSim.Types (ByteSize)
import Peras.Message (Message, NodeId)
import Peras.Orphans ()
import Test.QuickCheck (Arbitrary (..), frequency)
import Test.QuickCheck.Instances.Time ()

import qualified Data.Serialize as Serialize

data InEnvelope
  = InEnvelope
      { origin :: Maybe NodeId
      , inId :: UniqueId
      , inMessage :: Message
      }
  | Stop
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON InEnvelope
instance ToJSON InEnvelope

instance Arbitrary InEnvelope where
  arbitrary =
    frequency
      [ (9, InEnvelope <$> arbitrary <*> arbitrary <*> arbitrary)
      , (1, pure Stop)
      ]

data OutEnvelope
  = OutEnvelope
      { timestamp :: UTCTime
      , source :: NodeId
      , outMessage :: Message
      , outId :: UniqueId
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

mkUniqueId :: Hashable a => a -> UniqueId
mkUniqueId = UniqueId . Serialize.encode . hash
