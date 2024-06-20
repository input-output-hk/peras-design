{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}

module Peras.Voting.VoteSpec where

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Function ((&))
import Data.Maybe (mapMaybe)
import Data.Ratio ((%))
import Data.Word (Word64)
import Debug.Trace (trace)
import Peras.Voting.Vote (CommitteeSize, MembershipInput (..), RoundNumber (..), Voter (..), castVote, fromBytes, mkPartyId, newKESSigningKey, newVRFSigningKey, selectVote, voterStake, votingWeight)
import Test.Hspec (Spec, runIO)
import Test.Hspec.QuickCheck (modifyMaxSuccess, prop)
import Test.QuickCheck (Arbitrary, Gen, Property, arbitrary, choose, forAll, generate, property, tabulate, vectorOf, (===))

spec :: Spec
spec = do
  voters <- runIO $ generate $ genVoters 30
  prop "select committee size voters every round" $ trace (show voters) $ prop_selectCommitteeSizeVotersEveryRound voters
  modifyMaxSuccess (const 30) $
    prop "sortition selects committee shares according to relative weight" prop_sortitionSelectsVoterAccordingToWeight

prop_sortitionSelectsVoterAccordingToWeight :: Property
prop_sortitionSelectsVoterAccordingToWeight =
  forAll (choose (1_000_000, 100_000_000)) $ \committeeSize ->
    forAll (choose (1, 50)) $ \flipped ->
      let weight = selectVote committeeSize (flipped % 100) 10_000_000 200_000_000
          actual = fromIntegral weight % committeeSize
       in abs (actual - 5 % 100) <= 2 % 10000
            & tabulate "committee share" [show @Double ((fromIntegral $ floor $ 10000 * actual) / 100)]

genVoters :: Int -> Gen [Voter]
genVoters n = vectorOf n genVoter

genVoter :: Gen Voter
genVoter = do
  voterId <- mkPartyId <$> gen32Bytes
  voterStake <- choose (100_000_000, 100_000_000_000)
  vrfSignKey <- newVRFSigningKey <$> gen32Bytes
  let kesPeriod = 0
  kesSignKey <- newKESSigningKey <$> gen32Bytes
  pure $ MkVoter{voterId, voterStake, vrfSignKey, kesPeriod, kesSignKey}

instance Arbitrary RoundNumber where
  arbitrary = RoundNumber <$> choose (1, 1000000)

prop_selectCommitteeSizeVotersEveryRound :: [Voter] -> Property
prop_selectCommitteeSizeVotersEveryRound voters =
  forAll arbitrary $ \roundNumber ->
    forAll (fromBytes <$> gen32Bytes) $ \input ->
      forAll gen32Bytes $ \blockHash ->
        forAll (choose (60, 80)) $ \committeeRatio ->
          let totalStake = sum $ voterStake <$> voters
              committeeSize = fromInteger $ totalStake * committeeRatio `div` 100
              votes = mapMaybe (castVote blockHash totalStake input committeeSize roundNumber) voters
           in sum (votingWeight <$> votes) === fromIntegral committeeSize

gen32Bytes :: Gen ByteString
gen32Bytes = BS.pack <$> vectorOf 32 arbitrary
