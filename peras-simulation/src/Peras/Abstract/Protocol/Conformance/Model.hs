{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-name-shadowing -Wno-unused-matches #-}

module Peras.Abstract.Protocol.Conformance.Model where

import Control.Monad (guard)
import Peras.Abstract.Protocol.Params (PerasParams (MkPerasParams, perasA, perasB, perasL, perasT, perasU, perasτ), defaultPerasParams)
import Peras.Block (Block (MkBlock), Certificate (MkCertificate), Parties, PartyId, Tx)
import Peras.Chain (Chain, Vote)
import Peras.Crypto (Hash (MkHash), replicateBS)
import Peras.Numbering (RoundNumber (MkRoundNumber, getRoundNumber), SlotNumber (MkSlotNumber, getSlotNumber))
import qualified Peras.SmallStep (VotingRule'', preagreement)
import Relation.Nullary.Decidable.Core (isYes)

import Control.Monad.Identity
import Data.Function (on)
import Data.List (maximumBy)
import Data.Maybe (catMaybes, listToMaybe, maybeToList)
import Data.Ord (comparing)
import Data.Set (Set)
import qualified Data.Set as Set
import Peras.Abstract.Protocol.Crypto (createMembershipProof, createSignedCertificate, createSignedVote, mkCommitteeMember, mkParty)
import Peras.Abstract.Protocol.Fetching (findNewQuora)
import Peras.Abstract.Protocol.Voting (extends)
import Peras.Block (blockRef, certificate)
import Peras.Crypto (hash)
import Prelude hiding (round)

data NodeModel = NodeModel
  { clock :: SlotNumber
  , protocol :: PerasParams
  , allChains :: [Chain]
  , allVotes :: [Vote]
  , allSeenCerts :: [Certificate]
  }
  deriving (Eq, Show)

data EnvAction
  = Tick
  | NewChain Chain
  | NewVote Vote
  deriving (Eq, Show)

genesisHash :: Hash Block
genesisHash = MkHash (replicateBS 8 0)

genesisChain :: Chain
genesisChain = []

genesisCert :: Certificate
genesisCert = MkCertificate 0 genesisHash

initialModelState :: NodeModel
initialModelState =
  NodeModel
    1
    ( MkPerasParams
        5
        (perasA defaultPerasParams)
        1
        1
        1
        1
        (perasB defaultPerasParams)
        0
        0
    )
    [genesisChain]
    []
    [genesisCert]

sutId :: PartyId
sutId = 1

slotToRound :: PerasParams -> SlotNumber -> RoundNumber
slotToRound protocol (MkSlotNumber n) =
  MkRoundNumber (div n (perasU protocol))

slotInRound :: PerasParams -> SlotNumber -> SlotNumber
slotInRound protocol slot =
  MkSlotNumber (mod (getSlotNumber slot) (perasU protocol))

nextSlot :: SlotNumber -> SlotNumber
nextSlot (MkSlotNumber n) = MkSlotNumber (1 + n)

nextRound :: RoundNumber -> RoundNumber
nextRound (MkRoundNumber n) = MkRoundNumber (1 + n)

insertCert :: Certificate -> [Certificate] -> [Certificate]
insertCert cert [] = [cert]
insertCert cert (cert' : certs) =
  if cert == cert'
    then cert' : certs
    else cert' : insertCert cert certs

seenBeforeStartOfRound ::
  PerasParams -> RoundNumber -> (Certificate, SlotNumber) -> Bool
seenBeforeStartOfRound params r (c, s) =
  getSlotNumber s <= getRoundNumber r * perasU params

preferredChain :: PerasParams -> [Certificate] -> [Chain] -> Chain
preferredChain MkPerasParams{..} certs chains =
  maximumBy (compare `on` chainWeight perasB (Set.fromList certs)) (Set.fromList $ genesisChain : chains)

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

makeVote :: PerasParams -> SlotNumber -> Block -> Maybe Vote
makeVote protocol@MkPerasParams{perasT} slot block = do
  let r = slotToRound protocol slot
      party = mkCommitteeMember (mkParty 1 mempty [0 .. 10000]) protocol (slot - fromIntegral perasT) True
  Right proof <- createMembershipProof r (Set.singleton party)
  Right vote <- createSignedVote party r (hash block) proof 1
  pure vote

blockOldEnough :: PerasParams -> SlotNumber -> Block -> Bool
blockOldEnough params clock (MkBlock slot _ _ _ _ _ _) =
  getSlotNumber slot + perasL params + perasT params
    <= getSlotNumber clock

votesInState :: NodeModel -> [Vote]
votesInState s =
  maybeToList
    ( do
        guard (slotInRound params slot == 0)
        guard (isYes (Peras.SmallStep.VotingRule'' r s))
        makeVote params slot block
    )
 where
  params :: PerasParams
  params = protocol s
  slot :: SlotNumber
  slot = clock s
  r :: RoundNumber
  r = slotToRound params slot
  block :: Block
  block = Peras.SmallStep.preagreement slot s

newQuora :: Integer -> [Certificate] -> [Vote] -> [Certificate]
newQuora quorum priorCerts votes = newCerts
 where
  quora = findNewQuora (fromIntegral quorum) (Set.fromList priorCerts) (Set.fromList votes)
  Identity newCertsResults = mapM (createSignedCertificate $ mkParty 1 mempty [0 .. 10000]) quora
  newCerts = [c | Right c <- newCertsResults]

checkVoteSignature :: Vote -> Bool
checkVoteSignature _ = True -- TODO: could do actual crypto here

transition ::
  NodeModel -> EnvAction -> Maybe ([Vote], NodeModel)
transition s Tick =
  Just
    ( sutVotes
    , NodeModel
        (clock s')
        (protocol s')
        (allChains s')
        (sutVotes ++ allVotes s')
        (foldr insertCert (allSeenCerts s') certsFromQuorum)
    )
 where
  s' :: NodeModel
  s' =
    NodeModel
      (nextSlot (clock s))
      (protocol s)
      (allChains s)
      (allVotes s)
      (allSeenCerts s)
  sutVotes :: [Vote]
  sutVotes = votesInState s'
  certsFromQuorum :: [Certificate]
  certsFromQuorum =
    newQuora (perasτ (protocol s)) (allSeenCerts s) (allVotes s)
transition s (NewChain chain) =
  Just
    ( []
    , NodeModel
        (clock s)
        (protocol s)
        (chain : allChains s)
        (allVotes s)
        ( foldr
            insertCert
            (allSeenCerts s)
            (catMaybes $ map certificate chain)
        )
    )
transition s (NewVote v) =
  do
    guard (slotInRound (protocol s) (clock s) == 0)
    guard (checkVoteSignature v)
    Just
      ( []
      , NodeModel
          (clock s)
          (protocol s)
          (allChains s)
          (v : allVotes s)
          (allSeenCerts s)
      )