{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.RandomForks.Protocol (
  isCommitteeMember
, isFirstSlotInRound
, isSlotLeader
, mkProtocol
) where

import Peras.RandomForks.Types (Currency, Parameters(..), Protocol(..), Slot)
import System.Random.Stateful (StatefulGen, UniformRange(uniformRM))

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
