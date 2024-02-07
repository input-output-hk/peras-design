{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}

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
, Round
, Slot
, Vote(..)
) where

import Data.Default (Default(def))
import Data.ByteString.Short  (ShortByteString)

import qualified Data.Map.Strict as M
import qualified Data.Set as S

type BlockId = ShortByteString

type Currency = Int

type Slot = Int

type Round = Int

data Parameters =
  Parameters
  {
    peerCount :: Int
  , downstreamCount :: Int
  , maximumCurrency :: Currency
  , meanCommitteeSize :: Int
  , activeSlotCoefficient :: Double
  , roundDuration :: Int
  , votingBoost :: Double
  , votingWindow :: (Int, Int)
  , votingQuorum :: Double
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
    , roundDuration = 10
    , votingBoost = 0.25
    , votingWindow = (5, 20)
    , votingQuorum = 8
    }

data Protocol =
  Protocol
  {
    pSlotLottery :: Double
  , pCommitteeLottery :: Double
  , roundDuration :: Int
  , votingBoost :: Double
  , votingWindow :: (Int, Int)
  , votingQuorum :: Double
  }
    deriving stock (Eq, Ord, Read, Show)

newtype Peers = Peers {getPeers :: M.Map PeerName PeerState}
  deriving stock (Eq, Ord, Read, Show)

newtype PeerName = PeerName {getPeerName :: String}
  deriving stock (Eq, Ord, Read, Show)

data Vote =
  Vote
  {
    votingRound :: Round
  , voter :: PeerName    
  , votedBlock :: BlockId
  }
  deriving stock (Eq, Ord, Read, Show)

data Block =
  Block
  {
    creator :: PeerName
  , slot :: Slot
  , blockId :: BlockId
  , votes :: S.Set Vote
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
  , messageDestination :: PeerName
  , messageChain :: Chain
  , messageVotes :: S.Set Vote
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
  , danglingVotes :: S.Set Vote
  , pendingMessages :: [Message]
  }
    deriving stock (Eq, Ord, Read, Show)

data History =
  History
  {
    protocol :: Protocol
  , peerHistory :: M.Map Slot Peers
  }
    deriving stock (Eq, Ord, Read, Show)
