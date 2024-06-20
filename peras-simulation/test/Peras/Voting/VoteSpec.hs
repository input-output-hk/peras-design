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
import Peras.Voting.Vote (RoundNumber (..), Voter (..), castVote, fromBytes, mkPartyId, newKESSigningKey, newVRFSigningKey, selectVote, voterStake, votingWeight)
import Test.Hspec (Spec, runIO)
import Test.Hspec.QuickCheck (modifyMaxSuccess, prop)
import Test.QuickCheck (Arbitrary, Gen, Property, arbitrary, choose, counterexample, forAll, forAllBlind, generate, tabulate, vectorOf)

spec :: Spec
spec = do
  voters <- runIO $ generate $ genVoters 30
  modifyMaxSuccess (const 30) $ do
    prop "select committee size voters every round" $ prop_selectCommitteeSizeVotersEveryRound voters
    prop "sortition selects committee shares according to relative weight" prop_sortitionSelectsVoterAccordingToWeight

prop_sortitionSelectsVoterAccordingToWeight :: Property
prop_sortitionSelectsVoterAccordingToWeight =
  forAll (choose (1_000, 100_000)) $ \committeeSize ->
    forAll (choose (1, 50)) $ \flipped ->
      let weight = selectVote committeeSize (flipped % 100) 10_000 200_000
          actual = fromIntegral weight % committeeSize
       in abs (actual - 5 % 100) <= 2 % 10000
            & tabulate "committee share" [show @Double ((fromIntegral $ floor $ 10000 * actual) / 100)]

genVoters :: Int -> Gen [Voter]
genVoters n = vectorOf n genVoter

genVoter :: Gen Voter
genVoter = do
  voterId <- mkPartyId <$> gen32Bytes
  voterStake <- choose (1_000, 1_000_000) -- in ADA
  vrfSignKey <- newVRFSigningKey <$> gen32Bytes
  let kesPeriod = 0
  kesSignKey <- newKESSigningKey <$> gen32Bytes
  pure $ MkVoter{voterId, voterStake, vrfSignKey, kesPeriod, kesSignKey}

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
           in abs (totalVotes - fromIntegral committeeSize) < 10_000
                & counterexample ("totalVotes = " <> show totalVotes)
                & counterexample ("committeeSize = " <> show committeeSize)
                & counterexample ("difference = " <> show (abs (totalVotes - fromIntegral committeeSize)))

gen32Bytes :: Gen ByteString
gen32Bytes = BS.pack <$> vectorOf 32 arbitrary
