{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.MarkovSim.Decoupled where

import Peras.MarkovSim.Types
import Prelude hiding (round)

import qualified Data.HashMap.Strict as Map

step :: Peras -> Probabilities -> Evolution -> Evolution
step peras probabilities =
  let
    transition = Map.filter (/= 0) . blockCreation peras probabilities . tick peras
   in
    MkEvolution
      . Map.foldlWithKey'
        (\acc chains probability -> Map.unionWith (+) (Map.map (* probability) $ transition chains) acc)
        Map.empty
      . getEvolution

tick :: Peras -> Chains -> Chains
tick peras chains@MkChains{slot, honest, adversary} =
  -- Increment the slot number
  let chains' = chains{slot = slot + 1}
   in if newRound peras slot
        then -- Age the recent certificates.
          chains'{honest = tickCerts honest, adversary = tickCerts adversary}
        else chains'

tickCerts :: Chain -> Chain
tickCerts chain@MkChain{certUltimate, certPenultimate} =
  chain
    { -- No round-0 cert yet.
      certUltimate = False
    , -- The old round-0 cert becomes the round-1 cert.
      certPenultimate = certUltimate
    , -- The old round-1 cert becomes the round-2 cert.
      certAntepenultimate = certPenultimate
    }

blockCreation :: Peras -> Probabilities -> Chains -> Map.HashMap Chains Probability
blockCreation peras MkProbabilities{noBlock, honestBlock, adversaryBlock, mixedBlocks} chains@MkChains{slot, honest, adversary} =
  let
    round = inRound peras slot
    honest' = forgeBlock peras round honest
    adversary' = forgeBlock peras round adversary
   in
    -- FIXME: Handle common prefix.
    Map.fromList
      [ (chains, noBlock)
      , (chains{honest = honest'}, honestBlock)
      , (chains{adversary = adversary'}, adversaryBlock)
      , (chains{honest = honest', adversary = adversary'}, mixedBlocks)
      ]

forgeBlock :: Peras -> Round -> Chain -> Chain
forgeBlock MkPeras{a} round chain@MkChain{..} =
  let
    bc1a = not certAntepenultimate
    bc1b = round - certPrime <= a
    bc1c = certPrime > certStar
   in
    if bc1a && bc1b && bc1c
      then chain{weight = weight + 1, certStar = certPrime}
      else chain{weight = weight + 1}

voting :: Peras -> Probabilities -> Chains -> Map.HashMap Chains Probability
-- voting peras MkProbabilities{noQuorum, honestQuorum, adversaryQuorum,mixedQuorum} chains@MkChains{..} =
voting _ _ chains = Map.singleton chains 1
