{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.MarkovSim.Transition where

import Control.Arrow ((&&&))
import Control.Parallel.Strategies (parMap, rpar)
import Data.Bifunctor (second)
import Data.Function (on)
import Data.Map.Strict (Map)
import Data.Maybe (fromMaybe)
import Peras.MarkovSim.Types (
  AdverseAdoption (AdoptIfLonger, NeverAdopt),
  AdverseBlocks (DelayBlocks, PromptBlocks),
  AdverseCertification (DelayVotes, PromptVotes),
  AdverseRevelation (AlwaysReveal, NeverReveal, RevealIfLonger),
  AdverseSplitting (
    MkAdverseSplit,
    NoSplitting,
    splitFinish,
    splitStart
  ),
  AdverseVoting (AlwaysVote, NeverVote, VoteForAdversary),
  Behavior (..),
  Chain (..),
  Chains (..),
  Evolution (..),
  Peras (MkPeras, a, b, k, r),
  Probabilities (..),
  Probability,
  Slot,
  Thresholding (MkThreshold),
  inRound,
  newRound,
 )
import Prelude hiding (round)

import qualified Data.Map.Strict as Map

steps :: Double -> Peras -> Probabilities -> Int -> Evolution -> Evolution
steps ε peras probabilities n initial = foldr id initial . replicate n $ step ε peras probabilities

step :: Double -> Peras -> Probabilities -> Evolution -> Evolution
step ε peras probabilities =
  MkEvolution
    . Map.filter (> ε)
    . evolve (voting peras probabilities)
    . evolve (blockCreation peras probabilities . fetching peras . tick)
    . thresholdBehavior
    . getEvolution

evolve :: (Chains -> [(Chains, Probability)]) -> Map Chains Probability -> Map Chains Probability
evolve transition =
  Map.foldlWithKey'
    (\acc chains probability -> Map.unionWith (+) (Map.map (* probability) . Map.fromListWith (+) $ transition chains) acc)
    Map.empty

psteps :: Double -> Peras -> Probabilities -> Int -> Evolution -> Evolution
psteps ε peras probabilities n initial = foldr id initial . replicate n $ pstep ε peras probabilities

pstep :: Double -> Peras -> Probabilities -> Evolution -> Evolution
pstep ε peras probabilities =
  MkEvolution
    . Map.filter (> ε)
    . Map.unionsWith (+)
    . parMap rpar process
    . Map.toList
    . thresholdBehavior
    . getEvolution
 where
  blockCreation' = blockCreation peras probabilities . fetching peras . tick
  voting' = voting peras probabilities
  process (chains, probability) =
    Map.fromListWith (+)
      . concatMap (\(chains', probability') -> second (* (probability * probability')) <$> voting' chains')
      $ blockCreation' chains

tick :: Chains -> Chains
tick chains@MkChains{slot} =
  (crosschainBehavior chains)
    { -- Increment the slot number
      slot = slot + 1
    }

fetching :: Peras -> Chains -> Chains
fetching peras chains@MkChains{..} =
  let round = inRound peras slot
      receive chain@MkChain{..} =
        chain
          { -- Update cert*.
            certStar = fromMaybe certStar certStarNext
          , certStarNext = Nothing
          , -- Update cert'.
            certPrime = fromMaybe certPrime certPrimeNext
          , certPrimeNext = Nothing
          }
      update chain@MkChain{..} =
        chain
          { -- No round-0 cert yet.
            certUltimate = round == 0
          , -- The old round-0 cert becomes the round-1 cert.
            certPenultimate = certUltimate || round == 1
          , -- The old round-1 cert becomes the round-2 cert.
            certAntepenultimate = certPenultimate || round == 2
          }
      chains' =
        (updatePublicWeight chains)
          { -- Update cert* for the honest chain.
            honest = receive honest
          , -- Update cert* for the adversary chain.
            adversary = receive adversary
          }
   in if newRound peras slot
        then -- Age the recent certificates.

          chains'
            { honest = update honest
            , adversary = update adversary
            }
        else chains'

blockCreation :: Peras -> Probabilities -> Chains -> [(Chains, Probability)]
blockCreation peras@MkPeras{a} MkProbabilities{noBlock, honestBlock, adversaryBlock, mixedBlocks} chains@MkChains{..} =
  let
    round = inRound peras slot
    forge chain@MkChain{..} =
      let bc1a = not certAntepenultimate
          bc1c = certPrime > certStar
          bc1b = round - certPrime <= a
       in case adverseBlocks behavior of
            PromptBlocks ->
              if bc1a && bc1b && bc1c
                then
                  chain
                    { -- Add a block.
                      weight = weight + 1
                    , -- Include cert'.
                      certStarNext = Just certPrime
                    }
                else
                  chain
                    { -- Add a block.
                      weight = weight + 1
                    }
            DelayBlocks _ -> error "Not yet implemented: `DelayBlocks`."
    honest' = forge honest
    adversary' = forge adversary
   in
    clean
      [ (chains, noBlock)
      , (chains{honest = honest'}, honestBlock)
      , (chains{adversary = adversary'}, adversaryBlock)
      , (chains{honest = honest', adversary = adversary'}, mixedBlocks)
      ]

voting :: Peras -> Probabilities -> Chains -> [(Chains, Probability)]
voting peras@MkPeras{r, k, b} MkProbabilities{noQuorum, honestQuorum, adversaryQuorum, mixedQuorum} chains@MkChains{..} =
  let
    round = inRound peras slot
    vote chain@MkChain{..} =
      let vr1a = certPrime == round - 1
          vr1b = True -- FIXME: True by definition in these decoupled simulations.
          vr2a = round > certPrime + r
          vr2b = (round - certStar) `mod` k == 0
       in if vr1a && vr1b || vr2a && vr2b
            then case adverseCertification behavior of
              PromptVotes ->
                chain
                  { -- Boost the chain.
                    weight = weight + b
                  , -- Record the certificate.
                    certPrimeNext = Just round
                  }
              DelayVotes -> error "Not yet implemented: `DelayVotes`."
            else chain
   in
    if newRound peras slot
      then case adverseVoting behavior of
        NeverVote ->
          clean
            [ (chains, noQuorum + mixedQuorum + adversaryQuorum)
            , (chains{honest = vote honest}, honestQuorum)
            ]
        AlwaysVote ->
          clean
            [ (chains, noQuorum)
            , (chains{honest = vote honest}, honestQuorum + mixedQuorum)
            , (chains{adversary = vote adversary}, adversaryQuorum)
            ]
        VoteForAdversary ->
          clean
            [ (chains, noQuorum + mixedQuorum)
            , (chains{honest = vote honest}, honestQuorum)
            , (chains{adversary = vote adversary}, adversaryQuorum)
            ]
      else [(chains, 1)]

isSplit :: Behavior -> Slot -> Bool
isSplit MkBehavior{adverseSplitting} slot =
  case adverseSplitting of
    NoSplitting -> False
    MkAdverseSplit{splitStart, splitFinish} -> splitStart <= slot && slot <= splitFinish

thresholdBehavior :: Map Chains Probability -> Map Chains Probability
thresholdBehavior evolution
  | thresholding behavior == MkThreshold (slot + 1) =
      let
        evolution' = Map.filterWithKey (const . not . adversaryEverLonger) evolution
        mass = sum evolution'
       in
        Map.map (/ mass) evolution'
  | otherwise = evolution
 where
  MkChains{slot, behavior} = fst $ Map.findMin evolution

crosschainBehavior :: Chains -> Chains
crosschainBehavior chains@MkChains{..}
  | isSplit behavior slot = chains
  | otherwise =
      let
        communicateFromHonest =
          case adverseAdoption behavior of
            NeverAdopt -> False
            AdoptIfLonger -> weight honest > weight adversary
        communicateFromAdversary =
          case adverseRevelation behavior of
            NeverReveal -> False
            RevealIfLonger -> weight adversary > weight honest
            AlwaysReveal -> True
        mergeCerts :: Chain -> Chain -> Chain
        mergeCerts mine other =
          mine
            { certPrime = on max certPrime mine other
            , certPrimeNext = on max certPrimeNext mine other
            , certUltimate = on (||) certUltimate mine other
            , certPenultimate = on (||) certPenultimate mine other
            , certAntepenultimate = on (||) certAntepenultimate mine other
            }
        transferCertStar :: Chain -> Chain -> (Chain, Slot)
        transferCertStar mine other =
          if on (<) weight mine other
            then
              ( mine
                  { weight = weight other
                  , certStar = certStar other
                  , certStarNext = certStarNext other
                  }
              , weight other
              )
            else
              ( mine
              , prefix
              )
        communicate :: Chain -> Chain -> (Chain, Slot)
        communicate mine other =
          transferCertStar (mergeCerts mine other) other
        (honest', hprefix) =
          if communicateFromAdversary
            then communicate honest adversary
            else (honest, prefix)
        (adversary', aprefix) =
          if communicateFromHonest
            then communicate adversary honest
            else (adversary, prefix)
       in
        chains
          { prefix = max hprefix aprefix
          , honest = honest'
          , adversary = adversary'
          }

updatePublicWeight :: Chains -> Chains
updatePublicWeight chains@MkChains{honest, adversary, publicWeight, adversaryEverLonger} =
  let
    -- The honest weight is always a contender for the public weight of the tree.
    honestWeight = weight honest
    -- If the adversary chain just received a certificate, then their weight is a contender,
    -- but otherwise the previous public weight may represent their prior contension.
    adversaryWeight = weight adversary
    adversaryWeight' = maybe publicWeight (const adversaryWeight) $ certPrimeNext adversary
   in
    chains
      { publicWeight = max honestWeight adversaryWeight'
      , adversaryEverLonger = adversaryWeight > honestWeight || adversaryEverLonger
      }

clean :: [(a, Probability)] -> [(a, Probability)]
clean = filter $ (> 0) . snd

computeMargin :: Chains -> Int
computeMargin MkChains{publicWeight, honest, adversary} =
  on min weight honest adversary - publicWeight

computeReach :: Chains -> Int
computeReach MkChains{publicWeight, honest, adversary} =
  on max weight honest adversary - publicWeight

computeMarginReach :: Chains -> (Int, Int)
computeMarginReach = computeMargin &&& computeReach
