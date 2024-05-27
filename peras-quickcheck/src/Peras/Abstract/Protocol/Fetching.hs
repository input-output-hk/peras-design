{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

module Peras.Abstract.Protocol.Fetching (
  Fetching,
  fetching,
) where

import Control.Concurrent.Class.MonadSTM (MonadSTM, atomically, modifyTVar', readTVarIO)
import Control.Monad (unless, when)
import Control.Tracer (Tracer, traceWith)
import Data.Foldable (toList)
import Data.Function (on)
import Data.List (groupBy, maximumBy, sortBy)
import Data.Map as Map (fromList, keys, keysSet, notMember, union)
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import Data.Set as Set (fromList, intersection, map, size, union)
import Peras.Abstract.Protocol.Crypto (createSignedCertificate)
import Peras.Abstract.Protocol.Trace (PerasLog (..))
import Peras.Abstract.Protocol.Types (Fetching, PerasParams (..), PerasState (..), genesisCert)
import Peras.Block (Block (certificate), Certificate (..))
import Peras.Chain (Chain, Vote (MkVote, blockHash, votingRound))
import Peras.Crypto (hash)
import Prelude hiding (round)

fetching :: MonadSTM m => Tracer m PerasLog -> Fetching m
fetching tracer MkPerasParams{..} party stateVar slot newChains newVotes = do
  MkPerasState{..} <- readTVarIO stateVar
  -- 1. Fetch new chains Cnew and votes Vnew.
  traceWith tracer (NewChainAndVotes newChains newVotes)

  -- 2. Add any new chains in Cnew to C, add any new certificates contained in chains in Cnew to Certs.
  let chains' = chains `Set.union` newChains
      certsReceived =
        fmap (,slot)
          . filter (`Map.notMember` certs)
          . mapMaybe certificate
          . concat
          $ toList newChains
      certs'' = certs `Map.union` Map.fromList certsReceived

  unless (null certsReceived) $ traceWith tracer (NewCertificatesReceived certsReceived)

  -- 3. Add Vnew to V and turn any new quorum in V into a certificate cert
  let votes' = votes `Set.union` newVotes
      newQuora = findNewQuora (fromIntegral perasτ) (Map.keysSet certs'') votes' :: [Set Vote]
  newCertificatesFromQuorum <- fmap sequence (mapM (createSignedCertificate party) newQuora)

  case newCertificatesFromQuorum of
    -- FIXME: Simplify by lifting into `MonadError`.
    Left e -> pure $ Left e
    Right certsCreated -> do
      let certs' = certs'' `Map.union` Map.fromList ((,slot) <$> (certsCreated :: [Certificate]))
      unless (null certsCreated) $ traceWith tracer (NewCertificatesFromQuorum certsCreated)

      -- 4. Set Cpref to the heaviest (w.r.t. WtP(·)) valid chain in C .
      let chainPref' = maximumBy (compare `on` chainWeight perasB (Map.keysSet certs')) chains'
      when (chainPref' /= chainPref) $ traceWith tracer $ NewChainPref chainPref'

      -- 5. Set cert' to the certificate with the highest round number on Cpref.
      --
      -- FIXME: Figure 2 of the protocol does not specify which
      -- chain is preferred when there is a tie for heaviest
      -- chain.
      let certPrime' = maximumBy (compare `on` round) $ genesisCert : keys certs'
      when (certPrime' /= certPrime) $ traceWith tracer $ NewCertPrime certPrime'

      -- 6. Set cert* to the certificate with the highest round number on Cpref.
      --
      -- FIXME: There might be two alternative interpretations of
      -- "on C_pref":
      -- a) The certificates actually included in blocks of C_pref.
      -- b) Any certificate that references a block in C_pref.
      -- (Recall that certificates are not unconditionally
      -- included in blocks.) Here we adopt the first
      -- interpretation.
      let certStar' = maximumBy (compare `on` round) $ genesisCert : mapMaybe certificate chainPref'
      when (certStar' /= certStar) $ traceWith tracer $ NewCertStar certStar'

      fmap pure . atomically . modifyTVar' stateVar $ \state ->
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
