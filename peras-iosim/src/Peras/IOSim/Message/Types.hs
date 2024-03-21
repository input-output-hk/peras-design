{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NumericUnderscores #-}

module Peras.IOSim.Message.Types (
  InEnvelope (..),
  OutEnvelope (..),
  messageSize,
  mkUniqueId,
) where

import Control.Monad.Class.MonadTime (UTCTime)
import Data.Aeson (FromJSON, ToJSON)
import Data.Default (Default (..))
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

data MessageSizes = MessageSizes
  { sizeNextSlot :: ByteSize
  , sizeNewChain :: ByteSize
  , sizeSomeVote :: ByteSize
  , sizeFetchVotes :: ByteSize
  , sizeFollowChain :: ByteSize
  , sizeRollForward :: ByteSize
  , sizeRollBack :: ByteSize
  , sizeFetchBlocks :: ByteSize
  , sizeSomeBlock :: ByteSize
  }
  deriving stock (Eq, Generic, Read, Show)

instance FromJSON MessageSizes
instance ToJSON MessageSizes

instance Default MessageSizes where
  def =
    MessageSizes
      { sizeNextSlot = 0 -- Not a real message.
      , sizeNewChain = 1_100 -- Not a real message, but size it as the block header.
      , sizeSomeVote = 300 -- Just a guess.
      , sizeFetchVotes = 75 -- Size per vote hash.
      , sizeFollowChain = 75 -- Just a hash.
      , sizeRollForward = 1_100 -- Size of block header.
      , sizeRollBack = 1_100 -- Size of block header.
      , sizeFetchBlocks = 75 -- Size per vote hash.
      , sizeSomeBlock = 90_112 -- Worst case scenario.
      }

-- | The estimated serialized size of the message, in bytes
messageSize :: Message -> ByteSize
messageSize = \case
  NextSlot{} -> sizeNextSlot def
  NewChain{} -> sizeNewChain def
  SomeVote{} -> sizeSomeVote def
  FetchVotes vs -> sizeFetchVotes def * fromIntegral (length vs)
  FollowChain{} -> sizeFollowChain def
  RollForward{} -> sizeRollForward def
  RollBack{} -> sizeRollBack def
  FetchBlocks bs -> sizeFetchBlocks def * fromIntegral (length bs)
  SomeBlock{} -> sizeSomeBlock def

-- FIXME: Add TCP overhead.
