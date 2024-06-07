{-# LANGUAGE NamedFieldPuns #-}

module Peras.Abstract.Protocol.Network.Arbitrary where

import Control.Monad (filterM)
import Data.Default (def)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Peras.Abstract.Protocol.Network (PartyConfig (..), SimConfig (..))
import Peras.Abstract.Protocol.Types (PerasParams (..), systemStart)
import Peras.Numbering (SlotNumber)
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

exampleSimConfig :: SimConfig
exampleSimConfig =
  def
    { finish = 130
    , params =
        MkPerasParams
          { perasU = 20
          , perasA = 2160
          , perasR = 2
          , perasK = 3
          , perasL = 15
          , perasτ = 2
          , perasB = 100
          , perasT = 15
          , perasΔ = 2
          }
    , parties =
        Map.fromList
          [
            ( 1
            , MkPartyConfig
                { leadershipSlots = Set.fromList [2, 10, 25, 33, 39, 56, 71, 96, 101, 108, 109, 115]
                , membershipRounds = Set.fromList [1, 2, 6]
                , perasState = def
                }
            )
          ,
            ( 2
            , MkPartyConfig
                { leadershipSlots = Set.fromList [12, 17, 33, 44, 50, 67, 75, 88, 105]
                , membershipRounds = Set.fromList [2, 3, 5, 6]
                , perasState = def
                }
            )
          ,
            ( 3
            , MkPartyConfig
                { leadershipSlots = Set.fromList [5, 15, 42, 56, 71, 82, 124]
                , membershipRounds = Set.fromList [3, 4, 5, 6]
                , perasState = def
                }
            )
          ,
            ( 4
            , MkPartyConfig
                { leadershipSlots = Set.fromList [8, 15, 21, 38, 50, 65, 127]
                , membershipRounds = Set.fromList [1, 5]
                , perasState = def
                }
            )
          ]
    }
