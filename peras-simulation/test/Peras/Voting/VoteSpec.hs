{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Peras.Voting.VoteSpec where

import Cardano.Binary (serialize', unsafeDeserialize')
import qualified Cardano.Crypto.Hash as Hash
import Control.Monad (forM_)
import Data.Bits ((.&.), (.>>.))
import qualified Data.ByteString as BS
import Data.Function ((&))
import Data.Maybe (fromJust, mapMaybe)
import Data.Ratio ((%))
import Data.Word (Word64)
import Numeric (showFFloat)
import Peras.Voting.Arbitraries (applyMutation, gen32Bytes, genMutation, genOneVote, genVoters, mutationName)
import Peras.Voting.Vote (CommitteeSize, MembershipInput, RoundNumber (..), StakeDistribution, Vote (..), Voter (..), VotingParameters (..), asInteger, binomialVoteWeighing, castVote, castVote', checkVote, fromBytes, isLotteryWinner, mkStakeDistribution, voterStake, votingWeight)
import Test.Hspec (Spec, describe, it, runIO, shouldBe)
import Test.Hspec.QuickCheck (modifyMaxSuccess, prop, xprop)
import Test.QuickCheck (
  Arbitrary,
  Property,
  arbitrary,
  checkCoverage,
  choose,
  counterexample,
  cover,
  coverTable,
  elements,
  forAll,
  forAllBlind,
  generate,
  label,
  property,
  tabulate,
  (===),
 )

spec :: Spec
spec = do
  voters <- runIO $ generate $ genVoters 300
  prop "asInteger distributes hashes uniformly" $ prop_asIntegerDistributesHashesUniformly
  describe "Binomial Sortition" $ do
    prop "select committee size voters every round" $ prop_selectCommitteeSizeVotersEveryRound voters
    prop "sortition selects committee shares according to relative weight" prop_sortitionSelectsVoterAccordingToWeight
    prop "verifies valid votes" prop_verifiesValidVotes
    prop "rejects invalid votes" prop_rejectsInvalidVotes
  describe "Taylor-based Sortition" $ do
    forM_ [0.1, 0.2, 0.3, 0.5] $ \f ->
      forM_ [5, 10, 25, 50] $ \stakeRatio ->
        prop
          ( "lottery respects expected probabilities (stake = "
              <> show stakeRatio
              <> "%, f = "
              <> show f
              <> ")"
          )
          $ prop_lotteryRespectsExpectedProbabilities f (stakeRatio % 100)

    forM_ [1, 10, 25, 50, 100] $ \stakeRatio ->
      modifyMaxSuccess (const 1) $ do
        prop
          ( "Voter cast votes accoding to stake and parameters (stake = "
              <> show (fromIntegral stakeRatio / 10)
              <> "%)"
          )
          $ prop_voterCastsVotesAccordingToStakeAndParameters (head voters) (stakeRatio % 1000)
    modifyMaxSuccess (const 4) $ do
      xprop "selects committee size voters every round" $
        prop_selectVotersEveryRoundWithTaylorExpansion voters

  prop "can serialise and deserialise vote" prop_serialiseDeserialiseVote
  it "size of serialized vote for block hash is 676 bytes" $ do
    vote <- generate genOneVote
    let serialized = serialize' vote
    BS.length serialized `shouldBe` 676

prop_asIntegerDistributesHashesUniformly :: Property
prop_asIntegerDistributesHashesUniformly =
  forAll gen32Bytes $ \bytes -> do
    let i = asInteger (Hash.hashWith id bytes)
    property True
      & tabulate "distribution" [show $ i .&. 0xf]
      & coverTable "distribution" [(show j, 100 / 16) | j <- [0 .. 15]]
      & checkCoverage

prop_voterCastsVotesAccordingToStakeAndParameters :: Voter -> Rational -> Property
prop_voterCastsVotesAccordingToStakeAndParameters voter stakeRatio =
  forAllBlind (RoundNumber <$> choose (1, 100)) $ \roundNumber ->
    forAllBlind (fromBytes <$> gen32Bytes) $ \input ->
      forAllBlind gen32Bytes $ \block ->
        let totalStake = floor $ fromIntegral (voterStake voter) * recip stakeRatio
            params =
              VotingParameters
                { k = 2422
                , m = 20_973
                , f = 1 % 5
                }
            expected = 1 - (fromRational $ 4 % 5) ** fromRational stakeRatio
            vote = castVote' block totalStake input params roundNumber voter
         in case vote of
              Just MkVote{votingWeight} ->
                votingWeight === floor (expected * 20_973)
                  & cover (expected * 100 / 20_973) True ("expected wins = " <> show (floor $ expected * 20_973))
                  & checkCoverage
              Nothing -> property True

prop_lotteryRespectsExpectedProbabilities :: Double -> Rational -> Property
prop_lotteryRespectsExpectedProbabilities f stakeRatio =
  forAll (choose (0, maxBound @Word64 - 1)) $ \draw ->
    let c = log (1 - f)
        expected = 1 - (1 - f) ** fromRational stakeRatio
        win = isLotteryWinner (fromIntegral draw) (fromIntegral (maxBound :: Word64)) stakeRatio c
     in property True
          & cover (expected * 100) win ("expected win = " <> showFFloat (Just 2) (expected * 100) "%")
          & checkCoverage

prop_serialiseDeserialiseVote :: Property
prop_serialiseDeserialiseVote =
  forAllBlind gen32Bytes $ \block ->
    forAllVotes $ \input voters spos committeeSize ->
      forAllBlind (elements voters) $ \voter ->
        let totalStake = sum $ voterStake <$> voters
            vote = fromJust $ castVote block totalStake input committeeSize 42 voter
         in (unsafeDeserialize' . serialize' $ vote) === vote
              & counterexample ("vote = " <> show vote)

prop_rejectsInvalidVotes :: Property
prop_rejectsInvalidVotes =
  forAllBlind gen32Bytes $ \block ->
    forAllVotes $ \input voters spos committeeSize ->
      forAllBlind (elements voters) $ \voter ->
        let totalStake = sum $ voterStake <$> voters
            vote = fromJust $ castVote block totalStake input committeeSize 42 voter
         in forAll (genMutation voter vote) $ \mutation ->
              (checkVote committeeSize totalStake spos input . applyMutation mutation $ vote) === False
                & counterexample ("vote = " <> show vote)
                & tabulate "mutations" [mutationName mutation]
                & coverTable "mutations" [("MutateSignature", 30), ("MutateBlockHash", 30), ("MutateWeight", 30)]
                & checkCoverage

prop_verifiesValidVotes :: Property
prop_verifiesValidVotes =
  forAllBlind gen32Bytes $ \block ->
    forAllVotes $ \input voters spos committeeSize ->
      forAllBlind (elements voters) $ \voter ->
        let totalStake = sum $ voterStake <$> voters
            vote = castVote block totalStake input committeeSize 42 voter
         in (checkVote committeeSize totalStake spos input <$> vote) === Just True
              & counterexample ("vote = " <> show vote)

forAllVotes :: (MembershipInput -> [Voter] -> StakeDistribution -> CommitteeSize -> Property) -> Property
forAllVotes p =
  forAllBlind (fromBytes <$> gen32Bytes) $ \input ->
    forAllBlind (genVoters 10) $ \voters ->
      let totalStake = sum $ voterStake <$> voters
          spos = mkStakeDistribution voters
       in p input voters spos (fromIntegral totalStake `div` 2)

prop_sortitionSelectsVoterAccordingToWeight :: Property
prop_sortitionSelectsVoterAccordingToWeight =
  forAll (choose (1_000_000, 100_000_000)) $ \committeeSize ->
    forAll (choose (10, 50)) $ \flipped ->
      let expectedShare = 5 % 100

          totalStake :: Num a => a
          totalStake = 200_000_000

          tolerance = 5 % 10_000

          weight = binomialVoteWeighing committeeSize (flipped % 100) (floor $ expectedShare * totalStake) totalStake
          actual = fromIntegral weight % committeeSize
          diff = abs (actual - expectedShare)
       in diff <= tolerance
            & tabulate "committee share" [show @Double ((fromIntegral @Integer $ floor $ 10_000 * actual) / 100)]
            & counterexample ("actual = " <> show actual <> ", weight = " <> show weight <> ", diff = " <> show diff)

instance Arbitrary RoundNumber where
  arbitrary = RoundNumber <$> choose (1, 1000000)

prop_selectCommitteeSizeVotersEveryRound :: [Voter] -> Property
prop_selectCommitteeSizeVotersEveryRound voters =
  forAll arbitrary $ \roundNumber ->
    forAllBlind (fromBytes <$> gen32Bytes) $ \input ->
      forAllBlind gen32Bytes $ \block ->
        forAllBlind (choose (60, 80)) $ \committeeRatio ->
          let totalStake = sum $ voterStake <$> voters
              committeeSize = fromInteger $ totalStake * committeeRatio `div` 100
              votes = mapMaybe (castVote block totalStake input committeeSize roundNumber) voters
              totalVotes :: Integer = fromIntegral $ sum (votingWeight <$> votes)
              committeeSizeTolerance = floor @Rational ((5 % 10_000) * fromIntegral committeeSize)
           in abs (totalVotes - fromIntegral committeeSize) < committeeSizeTolerance
                & tabulate "committee ratio" [show committeeRatio]
                & counterexample ("totalVotes = " <> show totalVotes)
                & counterexample ("committeeSize = " <> show committeeSize)
                & counterexample ("difference = " <> show (abs (totalVotes - fromIntegral committeeSize)))

prop_selectVotersEveryRoundWithTaylorExpansion :: [Voter] -> Property
prop_selectVotersEveryRoundWithTaylorExpansion voters =
  forAll arbitrary $ \roundNumber ->
    forAllBlind (fromBytes <$> gen32Bytes) $ \input ->
      forAllBlind gen32Bytes $ \block ->
        let totalStake = sum $ voterStake <$> voters
            params =
              VotingParameters
                { k = 2422
                , m = 20973
                , f = 1 % 5
                }
            votes = mapMaybe (castVote' block totalStake input params roundNumber) voters
            totalVotes :: Integer = fromIntegral $ sum (votingWeight <$> votes)
         in property True
              & label ("votes = " <> show totalVotes)
