{-# LANGUAGE NamedFieldPuns #-}

module Peras.Prototype.Network.Arbitrary where

import Control.Monad (filterM)
import Data.Default (def)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Peras.Numbering (SlotNumber)
import Peras.Prototype.Network (PartyConfig (..), SimConfig (..))
import Peras.Prototype.Types (PerasParams (..), systemStart)
import Test.QuickCheck.Gen (Gen (MkGen), genDouble)
import Test.QuickCheck.Random (mkQCGen)

genSimConfigIO :: PerasParams -> Double -> Integer -> Integer -> SlotNumber -> Int -> IO SimConfig
genSimConfigIO params activeSlotCoefficient nParties nCommittee finish rngSeed =
  generateWith rngSeed $ genSimConfig params activeSlotCoefficient nParties nCommittee finish

generateWith :: Int -> Gen a -> IO a
generateWith seed (MkGen g) = pure $ mkQCGen seed `g` 30

genSimConfig :: PerasParams -> Double -> Integer -> Integer -> SlotNumber -> Gen SimConfig
genSimConfig params@MkPerasParams{perasU} activeSlotCoefficient nParties nCommittee finish =
  do
    let
      start = systemStart
      slots = [systemStart .. finish]
      rounds = fromIntegral <$> [(fromIntegral start `div` perasU + 1) .. (fromIntegral finish `div` perasU)]
      pLead = 1 - (1 - activeSlotCoefficient) ** (1 / fromIntegral nParties)
      pVote = fromIntegral nCommittee / fromIntegral nParties
      genLottery p = fmap Set.fromList . filterM (const $ (<= p) <$> genDouble)
      mkParty pid =
        do
          leadershipSlots <- genLottery pLead slots
          membershipRounds <- genLottery pVote rounds
          pure (pid, def{leadershipSlots, membershipRounds})
    parties <- Map.fromList <$> mapM mkParty [1 .. nParties]
    pure def{start, finish, params = params, parties}
