{-# LANGUAGE DerivingStrategies #-}

module Peras.RandomForks.Types (
  Block(..)
, BlockId
, Chain(..)
, Currency
, History(..)
, Message(..)
, Parameters(..)
, PeerName(..)
, PeerState(..)
, Peers(..)
, Protocol(..)
, Slot
) where

import Data.Default (Default(def))
import Data.ByteString.Short  (ShortByteString)

import qualified Data.Map.Strict as M
import qualified Data.Set as S

type BlockId = ShortByteString

type Currency = Int

type Slot = Int

data Parameters =
  Parameters
  {
    peerCount :: Int
  , downstreamCount :: Int
  , maximumCurrency :: Currency
  , activeSlotCoefficient :: Double
  , meanCommitteeSize :: Int
  , roundLength :: Int
  }
    deriving stock (Eq, Ord, Read, Show)

instance Default Parameters where
  def =
    Parameters
    {
      peerCount = 30
    , downstreamCount = 3
    , maximumCurrency = 1000
    , activeSlotCoefficient = 1 / 20
    , meanCommitteeSize = 10
    , roundLength = 5
    }

data Protocol =
  Protocol
  {
    pSlotLottery :: Double
  , pCommitteeLottery :: Double
  , roundDuration :: Int
  }
    deriving stock (Eq, Ord, Read, Show)

newtype Peers = Peers {getPeers :: M.Map PeerName PeerState}
  deriving stock (Eq, Ord, Read, Show)

newtype PeerName = PeerName {getPeerName :: String}
  deriving stock (Eq, Ord, Read, Show)

data Block =
  Block
  {
    creator :: PeerName
  , slot :: Slot
  , blockId :: BlockId
  }
    deriving stock (Eq, Ord, Read, Show)

data Chain =
  Chain
  {
    block :: Block,
    prev :: Chain
  }
  | Genesis
  deriving stock (Eq, Ord, Read, Show)

data Message =
  Message
  {
    messageSlot :: Slot
  , messageChain :: Chain
  , messageDestination :: PeerName
  }
    deriving stock (Eq, Ord, Read, Show)

data PeerState =
  PeerState
  {
    currency :: Currency
  , vrfOutput :: Double
  , slotLeader :: Bool
  , committeeMember :: Bool
  , upstream :: S.Set PeerName
  , downstream :: S.Set PeerName
  , preferredChain :: Chain
  , pendingMessages :: [Message]
  }
    deriving stock (Eq, Ord, Read, Show)

data History =
  History
  {
    _protocol :: Protocol
  , _peerHistory :: M.Map Slot Peers
  }
    deriving stock (Eq, Ord, Read, Show)
