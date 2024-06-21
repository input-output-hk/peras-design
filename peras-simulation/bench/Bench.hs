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
import Peras.Voting.Vote (Voter (voterStake), castVote, checkVote, fromBytes, mkStakeDistribution)
import Test.QuickCheck (Gen, arbitrary, elements, generate, vectorOf)

main :: IO ()
main = do
  voters <- generate $ genVoters 10000
  defaultMain
    [ bgroup
        "Committee Selection"
        [benchCommitteeSelection n voters | n <- [100, 500, 1000, 5000, 10000]]
    , benchVote voters
    , benchVerification voters
    ]

benchVerification :: [Voter] -> Benchmark
benchVerification voters =
  bench "Single Verification" $
    perRunEnv setup $ \ ~(blockHash, totalStake, input, committeeSize, spos, vote) ->
      evaluate $
        rnf $
          checkVote committeeSize totalStake spos input vote
 where
  setup = generate $ do
    blockHash <- gen32Bytes
    input <- fromBytes <$> gen32Bytes
    let totalStake = sum $ voterStake <$> voters
        committeeSize = fromInteger $ totalStake * 75 `div` 100
        roundNumber = 42
        spos = mkStakeDistribution voters
    voter <- elements voters
    let vote = fromJust $ castVote blockHash totalStake input committeeSize roundNumber voter
    pure (blockHash, totalStake, input, committeeSize, spos, vote)

benchVote :: [Voter] -> Benchmark
benchVote voters =
  bench "Single Voting" $
    perRunEnv setup $ \ ~(blockHash, totalStake, input, committeeSize, roundNumber, voter) ->
      evaluate $
        rnf $
          castVote blockHash totalStake input committeeSize roundNumber voter
 where
  setup = generate $ do
    blockHash <- gen32Bytes
    input <- fromBytes <$> gen32Bytes
    let totalStake = sum $ voterStake <$> voters
        committeeSize = fromInteger $ totalStake * 75 `div` 100
        roundNumber = 42
    voter <- elements voters
    pure (blockHash, totalStake, input, committeeSize, roundNumber, voter)

benchCommitteeSelection :: Int -> [Voter] -> Benchmark
benchCommitteeSelection numVoters voters =
  let
    label = show numVoters <> " voters"
    setup = generate $ do
      blockHash <- gen32Bytes
      input <- fromBytes <$> gen32Bytes
      let totalStake = sum $ voterStake <$> voters
          committeeSize = fromInteger $ totalStake * 75 `div` 100
          roundNumber = 42
      pure (blockHash, totalStake, input, committeeSize, roundNumber)
   in
    env setup $ \ ~(blockHash, totalStake, input, committeeSize, roundNumber) ->
      bench label $
        nf
          (mapMaybe (castVote blockHash totalStake input committeeSize roundNumber))
          (take numVoters voters)
