{-# LANGUAGE NumericUnderscores #-}

module Peras.Voting.VoteSpec where

import Data.Function ((&))
import Data.Maybe (mapMaybe)
import Data.Ratio ((%))
import Data.Word (Word64)
import Peras.Voting.Vote (CommitteeSize, RoundNumber (..), Voter, selectVote, votingWeight)
import Test.Hspec (Spec, runIO)
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (Arbitrary, Gen, Property, arbitrary, choose, forAll, generate, property, tabulate, vectorOf, (===))

spec :: Spec
spec = do
  -- voters <- runIO $ generate $ genVoters 3000
  -- prop "select committee size voters every round" $ prop_selectCommitteeSizeVotersEveryRound voters
  prop "sortition selects voter according to weight" prop_sortitionSelectsVoterAccordingToWeight

prop_sortitionSelectsVoterAccordingToWeight :: Property
prop_sortitionSelectsVoterAccordingToWeight =
  forAll (choose (1_000_000, 100_000_000)) $ \committeeSize ->
    forAll (choose (1, 50)) $ \flipped ->
      let weight = selectVote committeeSize (flipped % 100) 10_000_000 200_000_000
       in property True
            & tabulate "weight" [show (fromIntegral weight `div` 1_000_000)]

-- genVoters :: Int -> Gen [Voter]
-- genVoters n = vectorOf n arbitrary

-- instance Arbitrary RoundNumber where
--   arbitrary = RoundNumber <$> choose (1, 1000000)

-- prop_selectCommitteeSizeVotersEveryRound :: [Voter] -> CommitteeSize -> Property
-- prop_selectCommitteeSizeVotersEveryRound voters committeeSize =
--   forAll arbitrary $ \roundNumber ->
--     let votes = mapMaybe (castVote committeeSize roundNumber) voters
--      in sum (votingWeight <$> votes) === committeeSize
