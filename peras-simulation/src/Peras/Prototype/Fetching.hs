{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

module Peras.Prototype.Fetching (
  fetching,
  chainWeight,
  findNewQuora,
) where

import Control.Arrow ((&&&))
import Control.Concurrent.Class.MonadSTM (MonadSTM, TVar, atomically, modifyTVar', readTVarIO)
import Control.Monad (unless, when)
import Control.Monad.Except (ExceptT (ExceptT), runExceptT)
import Control.Monad.Trans (lift)
import Control.Tracer (Tracer, traceWith)
import Data.Foldable (toList)
import Data.Function (on)
import Data.List (groupBy, maximumBy, sortBy)
import Data.Map as Map (fromList, keys, keysSet, union)
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import qualified Data.Set as Set (filter, fromList, intersection, map, notMember, size, union)
import Peras.Block (Block (..), Certificate (..), Party (pid))
import Peras.Chain (Chain, Vote (MkVote, blockHash, votingRound))
import qualified Peras.Chain as Vote (Vote (creatorId, votingRound))
import Peras.Crypto (Hash, hash)
import Peras.Numbering (SlotNumber)
import Peras.Prototype.Crypto (createSignedCertificate)
import Peras.Prototype.Trace (PerasLog (..))
import Peras.Prototype.Types (PerasParams (..), PerasResult, PerasState (..), genesisCert)
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
        certsReceived = (,slot) <$> extractNewCertificates (Map.keysSet certs) newChains
        certsOldAndReceived = certs `Map.union` Map.fromList certsReceived
    unless (null certsReceived) . lift $ traceWith tracer (NewCertificatesReceived (pid party) certsReceived)

    -- 3. Add Vnew to V and turn any new quorum in V into a certificate cert.
    let equivocatedVote v = any (on (==) (Vote.votingRound &&& Vote.creatorId) v) votes
        unequivocatedVotes = Set.filter (not . equivocatedVote) newVotes
        votes' = votes `Set.union` unequivocatedVotes
        newQuora = findNewQuora (fromIntegral perasτ) (Map.keysSet certsOldAndReceived) votes'
    certsCreated <- ExceptT $ sequence <$> mapM (createSignedCertificate party) newQuora
    let certs' = certsOldAndReceived `Map.union` Map.fromList ((,slot) <$> certsCreated)
    unless (null certsCreated) . lift $ traceWith tracer (NewCertificatesFromQuorum (pid party) certsCreated)

    -- 4. Set Cpref to the heaviest (w.r.t. WtP(·)) valid chain in C .
    --
    -- NOTE: Resolve ties by comparing, in that order:
    --  * The slot number
    --  * The creator Id of the block
    --  * The hash of the block
    let chainPref' = maximumBy (compareChains perasB certs') chains'
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

compareChains perasB certs' a b =
  case (compare `on` chainWeight perasB (Map.keysSet certs')) a b of
    EQ ->
      let blocka = head a
          blockb = head b
       in case (compare `on` slotNumber) blocka blockb of
            EQ -> case (compare `on` creatorId) blocka blockb of
              EQ -> (compare `on` signature) blocka blockb
              x -> x
            x -> x
    x -> x

-- Find the new certificates in a set of chains.
extractNewCertificates :: Set Certificate -> Set Chain -> [Certificate]
extractNewCertificates certs =
  filter (`Set.notMember` certs) -- Ignore certificates already seen.
    . mapMaybe certificate -- Extract all certificates
    . concat
    . toList -- Consider all of the blocks from all of the chains.

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
