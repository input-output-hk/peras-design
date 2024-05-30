{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

module Peras.Abstract.Protocol.Fetching (
  fetching,
) where

import Control.Concurrent.Class.MonadSTM (MonadSTM, TVar, atomically, modifyTVar', readTVarIO)
import Control.Monad (unless, when)
import Control.Monad.Except (ExceptT (ExceptT), runExceptT)
import Control.Monad.Trans (lift)
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
import Peras.Abstract.Protocol.Types (PerasParams (..), PerasResult, PerasState (..), genesisCert)
import Peras.Block (Block (certificate), Certificate (..), Party (pid))
import Peras.Chain (Chain, Vote (MkVote, blockHash, votingRound))
import Peras.Crypto (Hash, hash)
import Peras.Numbering (SlotNumber)
import Prelude hiding (round)

-- At the beginning of each slot.
fetching ::
  MonadSTM m =>
  Tracer m PerasLog ->
  PerasParams ->
  Party ->
  TVar m PerasState ->
  SlotNumber ->
  Set Chain ->
  Set Vote ->
  m (PerasResult ())
fetching tracer MkPerasParams{..} party stateVar slot newChains newVotes =
  runExceptT $ do
    MkPerasState{..} <- lift $ readTVarIO stateVar

    -- 1. Fetch new chains Cnew and votes Vnew.
    lift . traceWith tracer $ NewChainAndVotes (pid party) newChains newVotes

    -- 2. Add any new chains in Cnew to C, add any new certificates contained in chains in Cnew to Certs.
    let chains' = chains `Set.union` newChains
        certsReceived =
          fmap (,slot) -- Record when each certificate was first received.
            . filter (`Map.notMember` certs) -- Ignore certificates already seen.
            . mapMaybe certificate
            . concat
            $ toList newChains -- Extract the certificates from the new chains.
        certsOldAndReceived = certs `Map.union` Map.fromList certsReceived
    unless (null certsReceived) . lift $ traceWith tracer (NewCertificatesReceived (pid party) certsReceived)

    -- 3. Add Vnew to V and turn any new quorum in V into a certificate cert.
    let votes' = votes `Set.union` newVotes
        newQuora = findNewQuora (fromIntegral perasτ) (Map.keysSet certsOldAndReceived) votes'
    certsCreated <- ExceptT $ sequence <$> mapM (createSignedCertificate party) newQuora
    let certs' = certsOldAndReceived `Map.union` Map.fromList ((,slot) <$> certsCreated)
    unless (null certsCreated) . lift $ traceWith tracer (NewCertificatesFromQuorum (pid party) certsCreated)

    -- 4. Set Cpref to the heaviest (w.r.t. WtP(·)) valid chain in C .
    --
    -- FIXME: Figure 2 of the protocol does not specify which chain is preferred
    -- when there is a tie for heaviest chain.
    let chainPref' = maximumBy (compare `on` chainWeight perasB (Map.keysSet certs')) chains'
    when (chainPref' /= chainPref) . lift $ traceWith tracer (NewChainPref (pid party) chainPref')

    -- 5. Set cert' to the certificate with the highest round number in Certs.
    --
    -- FIXME: If there are equivocations because of adversarial action, then there could be a tie
    -- for the certificate seen with the highest round.
    let certPrime' = maximumBy (compare `on` round) $ genesisCert : keys certs'
    when (certPrime' /= certPrime) . lift $ traceWith tracer (NewCertPrime (pid party) certPrime')

    -- 6. Set cert* to the certificate with the highest round number on Cpref.
    --
    -- FIXME: There might be two alternative interpretations of "on C_pref":
    -- a) The certificates actually included in blocks of C_pref.
    -- b) Any certificate that references a block in C_pref.
    -- (Recall that certificates are not unconditionally included in blocks.)
    -- Here we adopt the first interpretation.
    let certStar' = maximumBy (compare `on` round) $ genesisCert : mapMaybe certificate chainPref'
    when (certStar' /= certStar) . lift $ traceWith tracer (NewCertStar (pid party) certStar')

    -- Update the variables in the state.
    lift . atomically . modifyTVar' stateVar $ \state ->
      state
        { chainPref = chainPref'
        , chains = chains'
        , votes = votes'
        , certs = certs'
        , certPrime = certPrime'
        , certStar = certStar'
        }

-- Each party P assigns a certain weight to every chain C, based on C’s length
-- and all certificates that vote for blocks in C that P has seen so far.
chainWeight :: Integer -> Set Certificate -> Chain -> Integer
chainWeight boost certs blocks =
  let
    -- Block hashes certified by any certificate.
    certifiedBlocks = Set.map blockRef certs :: Set (Hash Block)
    -- Block hashes on the chain.
    chainBlocks = Set.fromList $ hash <$> blocks :: Set (Hash Block)
   in
    -- Length of the chain plus the boost times the count of certified blocks.
    fromIntegral (length blocks)
      + boost * fromIntegral (Set.size $ certifiedBlocks `Set.intersection` chainBlocks)

-- Find quora of votes that don't already have certificates.
--
-- FIXME: The `Vote` type does not record the weight of the vote, but this needs
-- to be accounted for when determining a quorum.
findNewQuora :: Int -> Set Certificate -> Set Vote -> [Set Vote]
findNewQuora quorum priorCerts votes =
  let
    -- A vote and a certificate certify the same block in the same round.
    sameCertification MkVote{votingRound, blockHash} MkCertificate{round, blockRef} =
      votingRound == round && blockHash == blockRef
    -- Order votes by round and then the hash of the block they vote for.
    orderVoting = on compare $ \MkVote{votingRound, blockHash} -> (votingRound, blockHash)
    -- Two votes vote for the same block in the same round.
    sameVoting = ((EQ ==) .) . orderVoting
    -- The votes that are not already represented by certificates.
    notAlreadyCertified =
      filter (\vote -> not $ any (sameCertification vote) $ toList priorCerts) $
        toList votes
    -- Uncertified votes grouped by round and the block being voted for.
    votesGrouped = groupBy sameVoting $ sortBy orderVoting notAlreadyCertified -- FIXME: We could use a map-reduce operation here.
   in
    -- Discard the sets of votes that are smaller than the quorum size.
    Set.fromList <$> filter ((>= quorum) . length) votesGrouped
