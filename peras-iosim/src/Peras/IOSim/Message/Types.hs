{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}

module Peras.IOSim.Message.Types (
  InEnvelope (..),
  OutEnvelope (..),
  messageSize,
  mkUniqueId,
) where

import Control.Monad.Class.MonadTime (UTCTime)
import Data.Aeson (FromJSON, ToJSON)
import Data.Hashable (Hashable, hash)
import GHC.Generics (Generic)
import Generic.Random (genericArbitrary, uniform)
import Peras.Arbitraries ()
import Peras.Event (ByteSize, UniqueId (..))
import Peras.Message (Message (..), NodeId)
import Peras.Orphans ()
import Test.QuickCheck (Arbitrary (..))
import Test.QuickCheck.Instances.Time ()

import qualified Data.Serialize as Serialize

data InEnvelope = InEnvelope
  { origin :: NodeId
  , inId :: UniqueId
  , inMessage :: Message
  , inTime :: UTCTime
  , inBytes :: ByteSize
  }
  deriving stock (Eq, Generic, Read, Show)

instance Ord InEnvelope where
  compare x y =
    compare
      (inTime x, inId x, origin x, inBytes x, inMessage x)
      (inTime y, inId y, origin y, inBytes y, inMessage y)

instance FromJSON InEnvelope
instance ToJSON InEnvelope

instance Arbitrary InEnvelope where
  arbitrary = genericArbitrary uniform

data OutEnvelope = OutEnvelope
  { source :: NodeId
  , destination :: NodeId
  , outId :: UniqueId
  , outMessage :: Message
  , outTime :: UTCTime
  , outBytes :: ByteSize
  }
  deriving stock (Eq, Generic, Read, Show)

instance Ord OutEnvelope where
  compare x y =
    compare
      (outTime x, outId x, source x, destination x, outBytes x, outMessage x)
      (outTime y, outId y, source y, destination y, outBytes y, outMessage y)

instance FromJSON OutEnvelope
instance ToJSON OutEnvelope

instance Arbitrary OutEnvelope where
  arbitrary = genericArbitrary uniform

mkUniqueId :: Hashable a => a -> UniqueId
mkUniqueId = UniqueId . Serialize.encode . hash

-- | The estimated serialized size of the message, in bytes
messageSize :: Message -> ByteSize
messageSize = \case
  NextSlot{} -> 0
  SomeBlock{} -> 72000 -- full body size at 80% load
  NewChain{} -> 1000 -- just the size of a header, checkout https://github.com/IntersectMBO/cardano-ledger/blob/master/eras/conway/impl/cddl-files/conway.cddl#L22
  SomeVote{} -> 300 -- FIXME
  _ -> 999 -- FIXME
