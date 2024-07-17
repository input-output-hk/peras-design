{-# LANGUAGE NumericUnderscores #-}

import Control.DeepSeq (rnf)
import Control.Exception (evaluate)
import Control.Monad (forM)
import Criterion (Benchmark, env, perRunEnv)
import Criterion.Main (bench, bgroup, defaultMain, nf, whnf)
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Maybe (fromJust, isJust, mapMaybe)
import Data.Word (Word8)
import Peras.Voting.Arbitraries (gen32Bytes, genVoters)
import Peras.Voting.Vote (Voter (voterStake), VotingParameters (..), castVote, castVote', checkVote, fromBytes, mkStakeDistribution)
import Test.QuickCheck (Gen, arbitrary, elements, generate, vectorOf)

main :: IO ()
main = do
  voters <- generate $ genVoters 10000
  defaultMain
    [ benchVote voters
    , benchVerification voters
    , benchVoteTaylor voters
    ]

benchVerification :: [Voter] -> Benchmark
benchVerification voters =
  bench "Single Verification" $
    perRunEnv setupVote $ \ ~(blockHash, totalStake, input, committeeSize, spos, vote) ->
      evaluate $
        rnf $
          checkVote committeeSize totalStake spos input vote
 where
  setupVote = do
    setup voters >>= \(blockHash, totalStake, input, committeeSize, roundNumber, voters) -> do
      voter <- generate $ elements voters
      let vote = fromJust $ castVote blockHash totalStake input committeeSize roundNumber voter
          spos = mkStakeDistribution voters
      pure (blockHash, totalStake, input, committeeSize, spos, vote)

benchVote :: [Voter] -> Benchmark
benchVote voters =
  bench "Single Voting (Binomial)" $
    perRunEnv setupVoter $ \ ~(blockHash, totalStake, input, committeeSize, roundNumber, voter) ->
      evaluate $
        rnf $
          castVote blockHash totalStake input committeeSize roundNumber voter
 where
  setupVoter = do
    setup voters >>= \(blockHash, totalStake, input, committeeSize, roundNumber, voters) -> do
      voter <- generate $ elements voters
      pure (blockHash, totalStake, input, committeeSize, roundNumber, voter)

benchVoteTaylor :: [Voter] -> Benchmark
benchVoteTaylor voters =
  bench "Single Voting (Taylor)" $
    perRunEnv setupVoter $ \ ~(blockHash, totalStake, input, roundNumber, voter) ->
      evaluate $
        rnf $
          castVote' blockHash totalStake input votingParameteers roundNumber voter
 where
  votingParameteers =
    VotingParameters
      { k = 2422
      , m = 20_973
      , f = 0.2
      }
  setupVoter = do
    setup voters >>= \(blockHash, totalStake, input, _, roundNumber, voters) -> do
      voter <- generate $ elements voters
      pure (blockHash, totalStake, input, roundNumber, voter)

setup voters = generate $ do
  blockHash <- gen32Bytes
  input <- fromBytes <$> gen32Bytes
  let totalStake = sum $ voterStake <$> voters
      committeeSize = fromInteger $ totalStake * 75 `div` 100
      roundNumber = 42
  pure (blockHash, totalStake, input, committeeSize, roundNumber, voters)
