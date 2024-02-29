{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.Protocol (
  newChain,
  nextSlot,
  candidateWindow,
  inclusionWindow,
  roundNumber,
  newVote,
) where

import Control.Lens (use, uses, (%=), (&), (.=))
import Control.Monad (replicateM)
import Control.Monad.Random (MonadRandom (getRandom, getRandomR))
import Control.Monad.State (MonadState)
import Data.Default (Default (def))
import Data.Function (on)
import Data.List (nub, partition)
import Data.Maybe (fromMaybe, mapMaybe)
import Numeric.Natural (Natural)
import Peras.Block (Block (Block, includedVotes, slotNumber), Slot)
import Peras.Chain (Chain (..), RoundNumber (RoundNumber), Vote (..))
import Peras.Crypto (Hash (Hash), LeadershipProof (LeadershipProof), MembershipProof (MembershipProof), Signature (Signature))
import Peras.IOSim.Hash (hashBlock, hashVote)
import Peras.IOSim.Node.Types (NodeState, activeVotes, blocksSeen, committeeMember, owner, preferredChain, rollbacks, slot, slotLeader, stake)
import Peras.IOSim.Protocol.Types (Protocol (..))
import Peras.IOSim.Types (Coin, Message', Rollback (..), Vote', Votes)
import Peras.Message (Message (NewChain, SomeVote))

import qualified Data.ByteString as BS
import qualified Data.Map as M
import qualified Data.Set as S

nextSlot ::
  MonadRandom m =>
  MonadState NodeState m =>
  Protocol ->
  Slot ->
  Coin ->
  m [Message']
nextSlot PseudoPraos{..} slotNumber total =
  do
    leader <- isSlotLeader activeSlotCoefficient total =<< use stake
    slot .= slotNumber
    slotLeader .= leader
    if leader
      then do
        creatorId <- use owner
        let parentBlock = Hash mempty -- FIXME: The Agda types don't yet have a structure for tracking block hashes.
            includedVotes = def
            payload = mempty
        leadershipProof <- LeadershipProof . BS.pack <$> replicateM 6 getRandom
        signature <- Signature . BS.pack <$> replicateM 6 getRandom
        chain <- preferredChain `uses` (\(MkChain blocks' votes') -> MkChain (Block slotNumber creatorId parentBlock includedVotes leadershipProof payload signature : blocks') votes')
        preferredChain .= chain
        pure [NewChain chain]
      else pure mempty
nextSlot PseudoPeras{..} slotNumber total =
  do
    -- FIXME: Consolidate code duplicated from `PseudoPraos`.
    let window = inclusionWindow voteMaximumAge slotNumber
    activeVotes %= discardExpiredVotes roundDuration window
    leader <- isSlotLeader activeSlotCoefficient total =<< use stake
    slot .= slotNumber
    slotLeader .= leader
    leaderMessages <-
      if leader
        then do
          creatorId <- use owner
          let parentBlock = Hash mempty -- FIXME: The Agda types don't yet have a structure for tracking block hashes.
              payload = mempty
          blocksSeen' <- use blocksSeen
          recordedBlocks <- use preferredChain
          allVotes <- use activeVotes
          recordedVotes <- preferredChain `uses` (M.restrictKeys allVotes . S.fromList . concatMap includedVotes . Peras.Chain.blocks)
          includedVotes <- activeVotes `uses` eligibleForInclusion blocksSeen' recordedBlocks recordedVotes window
          leadershipProof <- LeadershipProof . BS.pack <$> replicateM 6 getRandom
          signature <- Signature . BS.pack <$> replicateM 6 getRandom
          let block = Block slotNumber creatorId parentBlock (M.keys includedVotes) leadershipProof payload signature
          chain <- preferredChain `uses` (\(MkChain blocks' votes') -> MkChain (Block slotNumber creatorId parentBlock (M.keys includedVotes) leadershipProof payload signature : blocks') votes')
          preferredChain .= chain
          blocksSeen %= M.insert (hashBlock block) block
          pure [NewChain chain]
        else pure mempty
    -- FIXME: Maybe we should have a separate `nextRound` function?
    voterMessages <-
      if isNextRound roundDuration slotNumber
        then do
          let r = roundNumber roundDuration slotNumber
          votingAllowed <- preferredChain `uses` voteInRound roundDuration votingQuorum cooldownDuration r
          myself <- use owner
          voter <- isCommitteeMember pCommitteeLottery total =<< use stake
          committeeMember .= voter
          if voter && votingAllowed
            then do
              -- FIXME: The specification does not say which block in the window should be voted for, so choose the most recent one on the preferred chain.
              unrecordedVotes <- activeVotes `uses` M.filter ((== myself) . creatorId)
              preferredChain `uses` selectBlockInWindow unrecordedVotes (candidateWindow votingWindow slotNumber)
                >>= \case
                  Just block -> do
                    voteSignature <- Signature . BS.pack <$> replicateM 6 getRandom
                    proof <- MembershipProof . BS.pack <$> replicateM 6 getRandom
                    let vote =
                          MkVote
                            (fromIntegral $ slotNumber `div` roundDuration)
                            myself
                            proof
                            block
                            voteSignature
                    let voted = addVote vote block
                    blocksSeen %= M.insert (hashBlock voted) voted
                    activeVotes %= M.insert (hashVote vote) (vote{blockHash = hashBlock block})
                    pure [SomeVote vote]
                  Nothing -> pure mempty
            else pure mempty
        else pure mempty
    pure $ leaderMessages <> voterMessages
nextSlot OuroborosPraos{} _ _ = error "Ouroboros-Praos protocol is not yet implemented."
nextSlot OuroborosGenesis{} _ _ = error "Ouroboros-Genesis protocol is not yet implemented."
nextSlot OuroborosPeras{} _ _ = error "Ouroboros-Peras protocol is not yet implemented."

newChain ::
  MonadState NodeState m =>
  Protocol ->
  Chain ->
  m [Message']
newChain PseudoPraos{} chain =
  do
    let chainLength = Peras.Chain.blocks
    preferred <- use preferredChain
    if on (>) chainLength chain preferred
      then do
        preferredChain .= chain
        pure [NewChain chain]
      else pure mempty
newChain PseudoPeras{votingBoost} chain =
  do
    let chainLength chain' = sum $ (1 +) . (votingBoost *) . fromIntegral . length . includedVotes <$> Peras.Chain.blocks chain'
    preferred <- use preferredChain
    let fromWeight = chainLength preferred
        toWeight = chainLength chain
        checkRollback olds news =
          partition (`elem` Peras.Chain.blocks news) (Peras.Chain.blocks olds)
            & \case
              (_, []) -> pure ()
              (prefix, suffix) ->
                let
                  atSlot = if null prefix then 0 else slotNumber $ head prefix
                  slots = on (-) fromIntegral (slotNumber $ head suffix) atSlot
                  blocks = fromIntegral $ length suffix
                 in
                  rollbacks %= (Rollback{..} :)
    if toWeight > fromWeight
      then do
        checkRollback preferred chain
        preferredChain .= chain
        blocksSeen %= M.union (M.fromList [(hashBlock block, block) | block <- Peras.Chain.blocks chain])
        pure [NewChain chain]
      else newVotes $ Peras.Chain.votes chain
newChain OuroborosPraos{} _ = error "Ouroboros-Praos protocol is not yet implemented."
newChain OuroborosGenesis{} _ = error "Ouroboros-Genesis protocol is not yet implemented."
newChain OuroborosPeras{} _ = error "Ouroboros-Peras protocol is not yet implemented."

newVote ::
  MonadState NodeState m =>
  Protocol ->
  Vote Block ->
  m [Message']
newVote PseudoPraos{} _ = pure mempty
newVote PseudoPeras{} vote =
  do
    let
      hash = hashVote vote
      vote' = vote{blockHash = hashBlock $ blockHash vote}
    seen <- activeVotes `uses` M.member hash
    if seen
      then pure mempty
      else do
        activeVotes %= M.insert hash vote'
        pure [SomeVote vote]
newVote OuroborosPraos{} _ = error "Ouroboros-Praos protocol is not yet implemented."
newVote OuroborosGenesis{} _ = error "Ouroboros-Genesis protocol is not yet implemented."
newVote OuroborosPeras{} _ = error "Ouroboros-Peras protocol is not yet implemented."

newVotes ::
  MonadState NodeState m =>
  [Vote'] ->
  m [Message']
newVotes votes =
  do
    let votes' = M.fromList $ (\v -> (hashVote v, v)) <$> votes
    unseen <- activeVotes `uses` flip M.difference votes'
    if M.null unseen
      then pure mempty
      else do
        activeVotes %= M.union unseen
        let
          resolve vote =
            do
              block <- blocksSeen `uses` (fromMaybe (error "Block not present in `blocksSeen`!") . M.lookup (blockHash vote))
              pure . SomeVote $ vote{blockHash = block}
        mapM resolve $ M.elems unseen

isSlotLeader ::
  MonadRandom m =>
  Double ->
  Coin ->
  Coin ->
  m Bool
isSlotLeader activeSlotCoefficient' total staked =
  let p = 1 - (1 - activeSlotCoefficient') ** (fromIntegral staked / fromIntegral total)
   in (<= p) <$> getRandomR (0, 1)

isCommitteeMember ::
  MonadRandom m =>
  Double ->
  Coin ->
  Coin ->
  m Bool
isCommitteeMember pCommitteeLottery' _total staked =
  let p = 1 - (1 - pCommitteeLottery') ^ staked
   in (<= p) <$> getRandomR (0, 1)

candidateWindow ::
  (Natural, Natural) ->
  Slot ->
  (Slot, Slot)
candidateWindow (w0, w1) s =
  let
    s0 = s - min s (fromIntegral w0)
    s1 = s - min s (fromIntegral w1)
   in
    (min s0 s1, max s0 s1)

inclusionWindow ::
  Natural ->
  Slot ->
  (Slot, Slot)
inclusionWindow voteMaximumAge' s = (s - min s (fromIntegral voteMaximumAge'), s - min s 1)

roundNumber ::
  Natural ->
  Slot ->
  RoundNumber
roundNumber roundDuration' s = RoundNumber $ s `div` fromIntegral roundDuration'

isNextRound ::
  Natural ->
  Slot ->
  Bool
isNextRound roundDuration' s = s `mod` fromIntegral roundDuration' == 0

selectBlockInWindow ::
  Votes ->
  (Slot, Slot) ->
  Chain ->
  Maybe Block
selectBlockInWindow unrecordedVotes window chain =
  let
    blocksInWindow = filter ((`inWindow` window) . slotNumber) $ Peras.Chain.blocks chain
   in
    case filter ((`M.notMember` unrecordedVotes) . hashBlock) blocksInWindow of
      block : _ -> pure block
      [] -> Nothing

addVote ::
  Vote Block ->
  Block ->
  Block
addVote vote block =
  let
    vote' = vote{blockHash = block}
   in
    block{includedVotes = nub $ hashVote vote' : includedVotes block}

discardExpiredVotes ::
  Natural ->
  (Slot, Slot) ->
  M.Map Hash Vote' ->
  M.Map Hash Vote'
discardExpiredVotes roundDuration' window =
  M.filter $ \MkVote{votingRound} -> (fromIntegral votingRound * roundDuration') `inWindow` window

inWindow :: Ord a => a -> (a, a) -> Bool
inWindow x (xmin, xmax) = xmin <= x && x <= xmax

eligibleForInclusion ::
  M.Map Hash Block ->
  Chain ->
  Votes ->
  (Slot, Slot) ->
  Votes ->
  Votes
eligibleForInclusion blocksSeen' chain recordedVotes window candidateVotes =
  let
    checkCandidate vote@MkVote{blockHash} =
      let
        block = fromMaybe (error "Block not present in `blocksSeen`!") $ blockHash `M.lookup` blocksSeen' -- FIXME: Dangerous!
        windowOkay = slotNumber block `inWindow` window
        notRecorded = hashVote vote `M.notMember` recordedVotes
        blockOnChain = blockHash `elem` (hashBlock <$> Peras.Chain.blocks chain)
       in
        windowOkay && notRecorded && blockOnChain
   in
    M.filter checkCandidate candidateVotes

voteInRound ::
  Natural ->
  Int ->
  Natural ->
  RoundNumber ->
  Chain ->
  Bool
voteInRound roundDuration' votingQuorum' cooldownDuration' round' chain =
  let
    r = lastQuorum roundDuration' votingQuorum' chain
   in
    r + 1 == round' || r + fromIntegral cooldownDuration' <= round'

lastQuorum ::
  Natural ->
  Int ->
  Chain ->
  RoundNumber
lastQuorum roundDuration' votingQuorum' chain =
  let
    hasQuorum :: Block -> Maybe RoundNumber
    hasQuorum Block{slotNumber, includedVotes} =
      if length includedVotes >= votingQuorum'
        then Just . RoundNumber $ slotNumber `div` roundDuration'
        else Nothing
   in
    case mapMaybe hasQuorum $ Peras.Chain.blocks chain of
      r : _ -> r
      [] -> 0
