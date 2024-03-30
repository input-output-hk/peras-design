{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NumericUnderscores #-}

module Peras.IOSim.Cost (
  NodeCosts (..),
) where

import Data.Aeson (FromJSON, ToJSON)
import Data.Default (Default (..))
import Data.Ratio ((%))
import GHC.Generics (Generic)
import Peras.Event (CpuTime)

data NodeCosts = NodeCosts
  { costForgeBlock :: CpuTime
  -- ^ Slot leader forges a new block.
  , costCastVote :: CpuTime
  -- ^ Committee member casts a vote.
  , costEvaluateChain :: CpuTime
  -- ^ Weight a chain for adoption.
  , costRollForward :: CpuTime
  -- ^ Process
  , costRollBack :: CpuTime
  -- ^ Process a rollback message.
  , costFollowChain :: CpuTime
  -- ^ Process a chain-following message.
  , costVerifyVote :: CpuTime
  -- ^ Verify the validity of a vote.
  , costVerifyBlock :: CpuTime
  -- ^ Verify the validity of a block header.
  , costVerifyBody :: CpuTime
  -- ^ Verify the validity of a block body.
  , costReportVote :: CpuTime
  -- ^ Retrieve a vote from a local index.
  , costReportBlock :: CpuTime
  -- ^ Retrieve a block header from a local index.
  , costReportBody :: CpuTime
  -- ^ Retrieve a block body for a local index.
  , costRecordVote :: CpuTime
  -- ^ Store a vote in a local index.
  , costRecordBlock :: CpuTime
  -- ^ Store a block header in a local.
  , costRecordBody :: CpuTime
  -- ^ Store a block body in  a local
  , costRequestVote :: CpuTime
  -- ^ Decide to request a vote.
  , costRequestBlock :: CpuTime
  -- ^ Decide to request a block header.
  , costRequestBody :: CpuTime
  -- ^ Decide to request a block body.
  , costSendMessage :: CpuTime
  -- ^ Buffer and send a message to another node.
  }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON NodeCosts
instance ToJSON NodeCosts

instance Default NodeCosts where
  def =
    NodeCosts
      { costForgeBlock = fromRational $ 90 % 1_000_000
      , costCastVote = fromRational $ 75 % 1_000_000
      , costEvaluateChain = fromRational $ 40_000 % 1_000_000
      , costRollForward = fromRational $ 750 % 1_000_000
      , costRollBack = fromRational $ 700 % 1_000_000
      , costFollowChain = fromRational $ 50 % 1_000_000
      , costVerifyVote = fromRational $ 150 % 1_000_000
      , costVerifyBlock = fromRational $ 150 % 1_000_000
      , costVerifyBody = fromRational $ 150 % 1_000_000
      , costReportVote = fromRational $ 1_000 % 1_000_000
      , costReportBlock = fromRational $ 1_000 % 1_000_000
      , costReportBody = fromRational $ 2_000 % 1_000_000
      , costRecordVote = fromRational $ 3_000 % 1_000_000
      , costRecordBlock = fromRational $ 3_000 % 1_000_000
      , costRecordBody = fromRational $ 3_000 % 1_000_000
      , costRequestVote = fromRational $ 50 % 1_000_000
      , costRequestBlock = fromRational $ 50 % 1_000_000
      , costRequestBody = fromRational $ 50 % 1_000_000
      , costSendMessage = fromRational $ 100 % 1_000_000
      }
