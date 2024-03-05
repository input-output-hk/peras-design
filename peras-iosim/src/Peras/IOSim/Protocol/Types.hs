{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

module Peras.IOSim.Protocol.Types (
  Protocol (..),
  Invalid (..),
) where

import Control.Exception (Exception (..))
import Data.Aeson (FromJSON, ToJSON)
import Data.Default (Default (..))
import GHC.Generics (Generic)
import Numeric.Natural (Natural)

data Protocol = Peras
  { activeSlotCoefficient :: Double
  , pCommitteeLottery :: Double
  , roundDuration :: Natural
  , votingBoost :: Double
  , votingWindow :: (Natural, Natural)
  , votingQuorum :: Int
  , voteMaximumAge :: Natural
  , cooldownDuration :: Natural
  , prefixCutoffWeight :: Double
  }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance Default Protocol where
  def =
    Peras
      { activeSlotCoefficient = 0.05
      , roundDuration = 10
      , pCommitteeLottery = 0.00021
      , votingBoost = 0.25
      , votingWindow = (50, 1)
      , votingQuorum = 10
      , voteMaximumAge = 30
      , cooldownDuration = 5
      , prefixCutoffWeight = 10000000
      }

instance FromJSON Protocol
instance ToJSON Protocol

data Invalid
  = InvalidPraosChain
  | InvalidLeadershipProof
  | InvalidMembershipProof
  | InvalidBlockSignature
  | HashOfUnknownBlock
  | BlockIncludesUnknownVote
  | InvalidVoteSignature
  | HashOfUnknownVote
  | VoteReferencesUnknownBlock
  | VoteRecordedMultipleTimes
  | VoteNotAllowedInRound
  | VoteOutsideCandidateWindow
  | VoteOutsideInclusionWindow
  deriving stock (Bounded, Enum, Eq, Generic, Ord, Read, Show)

instance FromJSON Invalid
instance ToJSON Invalid

instance Exception Invalid where
  displayException = show
