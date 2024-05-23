{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

module Peras.Abstract.Protocol.Fetching (
  Fetching,
  fetching,
) where

import Control.Concurrent.STM (atomically)
import Control.Concurrent.STM.TVar (modifyTVar', readTVar)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.Foldable (toList)
import Data.Function (on)
import Data.List (groupBy, maximumBy, sortBy)
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import Peras.Abstract.Protocol.Crypto (createSignedCertificate)
import Peras.Abstract.Protocol.Types (Fetching, PerasParams (..), PerasState (..), genesisCert)
import Peras.Block (Block (certificate), Certificate (..))
import Peras.Chain (Chain, Vote (MkVote, blockHash, votingRound))
import Peras.Crypto (hash)
import Prelude hiding (round)

import Data.Map as Map (fromList, keys, keysSet, notMember, union)
import Data.Set as Set (fromList, intersection, map, size, union)

fetching :: MonadIO m => Fetching m
fetching MkPerasParams{..} party stateVar slot newChains newVotes =
  liftIO . atomically $ -- FIXME: Do we want fetching to be an atomic operation?
    do
      MkPerasState{..} <- readTVar stateVar
      let chains' = chains `Set.union` newChains
          votes' = votes `Set.union` newVotes
          certsReceived =
            filter (`Map.notMember` certs)
              . mapMaybe certificate
              . concat
              $ toList newChains
          certs'' = certs `Map.union` Map.fromList ((,slot) <$> certsReceived)
          newQuora = findNewQuora (fromIntegral perasτ) (Map.keysSet certs'') votes' :: [Set Vote]
      fmap sequence (mapM (createSignedCertificate party) newQuora)
        >>= \case
          -- FIXME: Simplify by lifting into `MonadError`.
          Left e -> pure $ Left e
          Right certsCreated ->
            do
              let certs' = certs'' `Map.union` Map.fromList ((,slot) <$> (certsCreated :: [Certificate]))
                  -- FIXME: Figure 2 of the protocol does not specify which
                  -- chain is preferred when there is a tie for weighiest
                  -- chain.
                  chainPref' = maximumBy (compare `on` chainWeight perasB (Map.keysSet certs')) chains'
                  certPrime' = maximumBy (compare `on` round) $ genesisCert : keys certs'
                  -- FIXME: Figure 2 of the protocol states "Set cert* to the
                  -- certificate with the highest round number on C_pref".
                  -- There might be two alternative interpretations of
                  -- "on C_pref":
                  -- a) The certificates actually included in blocks of C_pref.
                  -- b) Any certificate that references a block in C_pref.
                  -- (Recall that certificates are not unconditionally
                  -- included in blocks.) Here we adopt the first
                  -- interpretation.
                  certStar' = maximumBy (compare `on` round) $ genesisCert : mapMaybe certificate chainPref'
              fmap pure . modifyTVar' stateVar $ \state ->
                state
                  { chainPref = chainPref'
                  , chains = chains'
                  , votes = votes'
                  , certs = certs'
                  , certPrime = certPrime'
                  , certStar = certStar'
                  }

chainWeight :: Integer -> Set Certificate -> Chain -> Integer
chainWeight boost certs blocks =
  let
    certifiedBlocks = Set.map blockRef certs
    chainBlocks = Set.fromList $ hash <$> blocks
   in
    fromIntegral (length blocks)
      + boost * fromIntegral (Set.size $ certifiedBlocks `Set.intersection` chainBlocks)

findNewQuora :: Int -> Set Certificate -> Set Vote -> [Set Vote]
findNewQuora quorum priorCerts votes =
  let
    sameCertification MkVote{votingRound, blockHash} MkCertificate{round, blockRef} =
      votingRound == round && blockHash == blockRef
    orderVoting = on compare $ \MkVote{votingRound, blockHash} -> (votingRound, blockHash)
    sameVoting = ((EQ ==) .) . orderVoting
    notAlreadyCertified =
      filter (\vote -> not $ any (sameCertification vote) $ toList priorCerts) $
        toList votes
    votesGrouped = groupBy sameVoting $ sortBy orderVoting notAlreadyCertified
   in
    fmap Set.fromList $ filter ((>= quorum) . length) votesGrouped
