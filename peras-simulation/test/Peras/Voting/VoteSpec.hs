{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Peras.Voting.VoteSpec where

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Function ((&))
import Data.Maybe (mapMaybe)
import Data.Ratio ((%))
import Peras.Voting.Arbitraries (gen32Bytes, genVoters)
import Peras.Voting.Vote (RoundNumber (..), Voter (..), binomialVoteWeighing, castVote, fromBytes, mkPartyId, newKESSigningKey, newVRFSigningKey, voterStake, votingWeight)
import Test.Hspec (Spec, runIO)
import Test.Hspec.QuickCheck (modifyMaxSuccess, prop)
import Test.QuickCheck (Arbitrary, Gen, Property, arbitrary, choose, counterexample, forAll, forAllBlind, generate, tabulate, vectorOf)

spec :: Spec
spec = do
  voters <- runIO $ generate $ genVoters 30
  prop "select committee size voters every round" $ prop_selectCommitteeSizeVotersEveryRound voters
  prop "sortition selects committee shares according to relative weight" prop_sortitionSelectsVoterAccordingToWeight

prop_sortitionSelectsVoterAccordingToWeight :: Property
prop_sortitionSelectsVoterAccordingToWeight =
  forAll (choose (1_000_000, 100_000_000)) $ \committeeSize ->
    forAll (choose (10, 50)) $ \flipped ->
      let weight = binomialVoteWeighing committeeSize (flipped % 100) 10_000_000 200_000_000
          actual = fromIntegral weight % committeeSize
          diff = abs (actual - 5 % 100)
       in diff <= 5 % 10000
            & tabulate "committee share" [show @Double ((fromIntegral $ floor $ 10000 * actual) / 100)]
            & counterexample ("actual = " <> show actual <> ", weight = " <> show weight <> ", diff = " <> show diff)

instance Arbitrary RoundNumber where
  arbitrary = RoundNumber <$> choose (1, 1000000)

prop_selectCommitteeSizeVotersEveryRound :: [Voter] -> Property
prop_selectCommitteeSizeVotersEveryRound voters =
  forAll arbitrary $ \roundNumber ->
    forAllBlind (fromBytes <$> gen32Bytes) $ \input ->
      forAllBlind gen32Bytes $ \blockHash ->
        forAllBlind (choose (60, 80)) $ \committeeRatio ->
          let totalStake = sum $ voterStake <$> voters
              committeeSize = fromInteger $ totalStake * committeeRatio `div` 100
              votes = mapMaybe (castVote blockHash totalStake input committeeSize roundNumber) voters
              totalVotes :: Integer = fromIntegral $ sum (votingWeight <$> votes)
           in abs (totalVotes - fromIntegral committeeSize) < 2_000_000
                & tabulate "committee ratio" [show committeeRatio]
                & counterexample ("totalVotes = " <> show totalVotes)
                & counterexample ("committeeSize = " <> show committeeSize)
                & counterexample ("difference = " <> show (abs (totalVotes - fromIntegral committeeSize)))
