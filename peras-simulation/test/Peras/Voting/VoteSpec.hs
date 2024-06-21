{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Peras.Voting.VoteSpec where

import Data.ByteString (ByteString)
import Data.Function ((&))
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Maybe (fromJust, mapMaybe)
import Data.Ratio ((%))
import Peras.Voting.Arbitraries (applyMutation, gen32Bytes, genMutation, genVoters, mutationName)
import Peras.Voting.Vote (CommitteeSize, MembershipInput, RoundNumber (..), Signature, StakeDistribution, Vote (..), Voter (..), binomialVoteWeighing, castVote, checkVote, fromBytes, voterStake, votingWeight)
import Test.Hspec (Spec, runIO)
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (Arbitrary, Gen, Property, arbitrary, choose, counterexample, elements, forAll, forAllBlind, generate, tabulate, (===))

spec :: Spec
spec = do
  voters <- runIO $ generate $ genVoters 30
  prop "select committee size voters every round" $ prop_selectCommitteeSizeVotersEveryRound voters
  prop "sortition selects committee shares according to relative weight" prop_sortitionSelectsVoterAccordingToWeight
  prop "verifies valid votes" prop_verifiesValidVotes
  prop "rejects invalid votes" prop_rejectsInvalidVotes

prop_rejectsInvalidVotes :: Property
prop_rejectsInvalidVotes =
  forAllBlind gen32Bytes $ \blockHash ->
    forAllVotes $ \input voters spos committeeSize ->
      forAllBlind (elements voters) $ \voter ->
        let totalStake = sum $ voterStake <$> voters
            vote = fromJust $ castVote blockHash totalStake input committeeSize 42 voter
         in forAll (genMutation voter vote) $ \mutation ->
              (checkVote spos input . applyMutation mutation $ vote) === False
                & counterexample ("vote = " <> show vote)
                & tabulate "mutation" [mutationName mutation]

prop_verifiesValidVotes :: Property
prop_verifiesValidVotes =
  forAllBlind gen32Bytes $ \blockHash ->
    forAllVotes $ \input voters spos committeeSize ->
      forAllBlind (elements voters) $ \voter ->
        let totalStake = sum $ voterStake <$> voters
            vote = castVote blockHash totalStake input committeeSize 42 voter
         in (checkVote spos input <$> vote) === Just True
              & counterexample ("vote = " <> show vote)

forAllVotes :: (MembershipInput -> [Voter] -> StakeDistribution -> CommitteeSize -> Property) -> Property
forAllVotes p =
  forAllBlind (fromBytes <$> gen32Bytes) $ \input ->
    forAllBlind (genVoters 10) $ \voters ->
      let totalStake = sum $ voterStake <$> voters
          spos =
            Map.fromList $
              [ (voterId, (vrfVerKey, kesVerKey, voterStake))
              | MkVoter{voterId, vrfVerKey, kesVerKey, voterStake} <- voters
              ]
       in p input voters spos (fromIntegral totalStake `div` 2)

prop_sortitionSelectsVoterAccordingToWeight :: Property
prop_sortitionSelectsVoterAccordingToWeight =
  forAll (choose (1_000_000, 100_000_000)) $ \committeeSize ->
    forAll (choose (10, 50)) $ \flipped ->
      let weight = binomialVoteWeighing committeeSize (flipped % 100) 10_000_000 200_000_000
          actual = fromIntegral weight % committeeSize
          diff = abs (actual - 5 % 100)
       in diff <= 5 % 10_000
            & tabulate "committee share" [show @Double ((fromIntegral $ floor $ 10_000 * actual) / 100)]
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
