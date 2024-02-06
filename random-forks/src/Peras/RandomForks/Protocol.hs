{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.RandomForks.Protocol (
  Parameters(..)
, Protocol(..)
, isCommitteeMember
, isFirstSlotInRound
, isSlotLeader
, mkProtocol
) where

import Data.Default (Default(..))
import Peras.RandomForks.Types (Currency, Slot)
import System.Random.Stateful (StatefulGen, UniformRange(uniformRM))

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
    deriving (Eq, Ord, Read, Show)

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
    deriving (Eq, Ord, Read, Show)

mkProtocol
  :: Parameters
  -> Protocol
mkProtocol Parameters{..} =
  let
    expectedStake = fromIntegral $ peerCount * maximumCurrency `div` 2
    pSlotLottery = 1 - (1 - activeSlotCoefficient) ** (1 / expectedStake)
    -- FIXME: These formulae are approximate--the real one is lengthy.
    fractionInCommittee = fromIntegral meanCommitteeSize / fromIntegral peerCount
    pCommitteeLottery = 1 - (1 - fractionInCommittee) ** (2 / fromIntegral maximumCurrency)
    roundDuration = roundLength
  in
    Protocol{..}

isSlotLeader
  :: StatefulGen g m
  => g
  -> Protocol
  -> Currency
  -> m Bool
isSlotLeader gen Protocol{pSlotLottery} currency =
  -- FIXME: This is just a crude approximation to the actual Praos leader-selection algorithm.
  let
     p = 1 - (1 - pSlotLottery)^currency
  in
    (<= p) <$> uniformRM (0, 1) gen

isCommitteeMember
  :: StatefulGen g m
  => g
  -> Protocol
  -> Currency
  -> m Bool
isCommitteeMember gen Protocol{pCommitteeLottery} currency =
  let
     p = 1 - (1 - pCommitteeLottery)^currency
  in
    (<= p) <$> uniformRM (0, 1) gen

isFirstSlotInRound
  :: Protocol
  -> Slot
  -> Bool
isFirstSlotInRound Protocol{roundDuration} slot = slot `mod` roundDuration == 0
