{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.RandomForks.Protocol (
  Parameters (..),
  Protocol (..),
  mkProtocol,
  isSlotLeader,
  isCommitteMember,
) where

import Data.Default (Default (..))
import Peras.RandomForks.Types (Currency)
import System.Random (randomRIO)

data Parameters = Parameters
  { peerCount :: Int
  , downstreamCount :: Int
  , maximumCurrency :: Currency
  , activeSlotCoefficient :: Double
  , meanCommitteeSize :: Int
  }
  deriving (Eq, Ord, Read, Show)

instance Default Parameters where
  def =
    Parameters
      { peerCount = 10
      , downstreamCount = 3
      , maximumCurrency = 1000
      , activeSlotCoefficient = 1 / 20
      , meanCommitteeSize = 6
      }

data Protocol = Protocol
  { pSlotLottery :: Double
  , pCommitteeLottery :: Double
  }
  deriving (Eq, Ord, Read, Show)

mkProtocol ::
  Parameters ->
  Protocol
mkProtocol Parameters{..} =
  let
    expectedStake = fromIntegral $ peerCount * maximumCurrency `div` 2
    pSlotLottery = 1 - (1 - activeSlotCoefficient) ** (1 / expectedStake)
    -- FIXME: These formulae are approximate--the real one is lengthy.
    fractionInCommittee = fromIntegral meanCommitteeSize / fromIntegral peerCount
    pCommitteeLottery = 1 - (1 - fractionInCommittee) ** (2 / fromIntegral maximumCurrency)
   in
    Protocol{..}

isSlotLeader ::
  Protocol ->
  Currency ->
  IO Bool
isSlotLeader Protocol{pSlotLottery} currency =
  -- FIXME: This is just a crude approximation to the actual Praos leader-selection algorithm.
  let
    p = 1 - (1 - pSlotLottery) ^ currency
   in
    (<= p) <$> randomRIO (0, 1)

isCommitteMember ::
  Protocol ->
  Currency ->
  IO Bool
isCommitteMember Protocol{pCommitteeLottery} currency =
  let
    p = 1 - (1 - pCommitteeLottery) ^ currency
   in
    (<= p) <$> randomRIO (0, 1)
