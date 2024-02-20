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

import Control.Lens (use, uses, (%=), (.=))
import Control.Monad (replicateM)
import Control.Monad.Random (MonadRandom (getRandom, getRandomR))
import Control.Monad.State (MonadState)
import Data.Default (Default (def))
import Data.Function (on)
import Peras.Block (Block (Block, includedVotes, signature, slotNumber), Slot)
import Peras.Chain (Chain (..), asList)
import Peras.Crypto (Hash (Hash), LeadershipProof (LeadershipProof), Signature (Signature))
import Peras.IOSim.Node.Types (NodeState, activeVotes, committeeMember, owner, preferredChain, slot, slotLeader, stake)
import Peras.IOSim.Protocol.Types (Protocol (..))
import Peras.IOSim.Types (Coin, Round, Vote (..), Votes)
import Peras.Message (Message (NewChain, SomeBlock))

import qualified Data.ByteString as BS
import qualified Data.Set as S

nextSlot ::
  MonadRandom m =>
  MonadState NodeState m =>
  Protocol ->
  Slot ->
  Coin ->
  m [Message Votes]
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
        chain <- preferredChain `uses` Cons (Block slotNumber creatorId parentBlock includedVotes leadershipProof payload signature)
        preferredChain .= chain
        pure [NewChain chain]
      else pure mempty
nextSlot PseudoPeras{..} slotNumber total =
  do
    -- FIXME: Consolidate code duplicated from `PseudoPraos`.
    let window = inclusionWindow voteMaximumAge slotNumber
    activeVotes %= discardExpiredVotes window
    leader <- isSlotLeader activeSlotCoefficient total =<< use stake
    slot .= slotNumber
    slotLeader .= leader
    leaderMessages <-
      if leader
        then do
          creatorId <- use owner
          let parentBlock = Hash mempty -- FIXME: The Agda types don't yet have a structure for tracking block hashes.
              payload = mempty
          recordedBlocks <- preferredChain `uses` asList
          recordedVotes <- preferredChain `uses` (S.unions . fmap includedVotes . asList)
          includedVotes <- activeVotes `uses` eligibleForInclusion recordedBlocks recordedVotes window
          leadershipProof <- LeadershipProof . BS.pack <$> replicateM 6 getRandom
          signature <- Signature . BS.pack <$> replicateM 6 getRandom
          chain <- preferredChain `uses` Cons (Block slotNumber creatorId parentBlock includedVotes leadershipProof payload signature)
          preferredChain .= chain
          pure [NewChain chain]
        else pure mempty
    -- FIXME: Maybe we should have a separate `nextRound` function?
    voterMessages <-
      if isNextRound roundDuration slotNumber
        then do
          myself <- use owner
          voter <- isCommitteeMember pCommitteeLottery total =<< use stake
          committeeMember .= voter
          if voter
            then do
              -- FIXME: The specification does not say which block in the window should be voted for, so choose the most recent one on the preferred chain.
              unrecordedVotes <- activeVotes `uses` S.filter ((== myself) . Peras.IOSim.Types.voter)
              preferredChain `uses` selectBlockInWindow unrecordedVotes (candidateWindow votingWindow slotNumber)
                >>= \case
                  Just block -> do
                    voteSignature <- Signature . BS.pack <$> replicateM 6 getRandom
                    let vote = Vote (slotNumber `div` fromIntegral roundDuration) voteSignature block myself
                    let voted = addVote vote block
                    activeVotes %= S.insert vote
                    pure [SomeBlock voted]
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
  Chain Votes ->
  m [Message Votes]
newChain PseudoPraos{} chain =
  do
    let chainLength Genesis = (0 :: Int)
        chainLength (Cons _ chain') = 1 + chainLength chain'
    preferred <- use preferredChain
    if on (>) chainLength chain preferred
      then do
        preferredChain .= chain
        pure [NewChain chain]
      else pure mempty
newChain protocol@PseudoPeras{votingBoost} chain =
  do
    mapM_ (newVote protocol) . concatMap (S.toList . includedVotes) $ asList chain
    let chainLength Genesis = 0
        chainLength (Cons Block{includedVotes} chain') = 1 + chainLength chain' + votingBoost * fromIntegral (S.size includedVotes)
    preferred <- use preferredChain
    if on (>) chainLength chain preferred
      then do
        preferredChain .= chain
        pure [NewChain chain]
      else pure mempty
newChain OuroborosPraos{} _ = error "Ouroboros-Praos protocol is not yet implemented."
newChain OuroborosGenesis{} _ = error "Ouroboros-Genesis protocol is not yet implemented."
newChain OuroborosPeras{} _ = error "Ouroboros-Peras protocol is not yet implemented."

newVote ::
  MonadState NodeState m =>
  Protocol ->
  Vote ->
  m ()
newVote PseudoPraos{} _ = pure ()
newVote PseudoPeras{} vote = activeVotes %= S.insert vote
newVote OuroborosPraos{} _ = error "Ouroboros-Praos protocol is not yet implemented."
newVote OuroborosGenesis{} _ = error "Ouroboros-Genesis protocol is not yet implemented."
newVote OuroborosPeras{} _ = error "Ouroboros-Peras protocol is not yet implemented."

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
isCommitteeMember pCommitteeLottery' total staked =
  let p = 1 - (1 - pCommitteeLottery') ** (fromIntegral staked / fromIntegral total)
   in (<= p) <$> getRandomR (0, 1)

candidateWindow ::
  (Int, Int) ->
  Slot ->
  (Slot, Slot)
candidateWindow (w0, w1) s =
  let
    s0 = s - min s (fromIntegral w0)
    s1 = s - min s (fromIntegral w1)
   in
    (min s0 s1, max s0 s1)

inclusionWindow ::
  Int ->
  Slot ->
  (Slot, Slot)
inclusionWindow voteMaximumAge' s = (s - min s (fromIntegral voteMaximumAge'), s - min s 1)

roundNumber ::
  Int ->
  Slot ->
  Round
roundNumber roundDuration' s = s `div` fromIntegral roundDuration'

isNextRound ::
  Int ->
  Slot ->
  Bool
isNextRound roundDuration' s = s `mod` fromIntegral roundDuration' == 0

selectBlockInWindow ::
  Votes ->
  (Slot, Slot) ->
  Chain Votes ->
  Maybe (Block Votes)
selectBlockInWindow unrecordedVotes window chain =
  let
    blocksInWindow = filter ((`inWindow` window) . slotNumber) $ asList chain
   in
    case filter ((`S.notMember` S.map (signature . voteForBlock) unrecordedVotes) . signature) blocksInWindow of
      block : _ -> pure block
      _ -> Nothing

addVote ::
  Vote ->
  Block Votes ->
  Block Votes
addVote vote block =
  if False
    then -- FIXME: We probably shouldn't tie the knot here, but this is a workaround until the Agda is more mature.

      let
        vote' = vote{voteForBlock = block'}
        block' = block{includedVotes = vote' `S.insert` includedVotes block}
       in
        block'
    else
      let
        -- FIXME: We probably shouldn't tie the knot here, but this is a workaround until the Agda is more mature.
        vote' = vote{voteForBlock = block}
       in
        block{includedVotes = S.singleton vote'}

discardExpiredVotes ::
  (Slot, Slot) ->
  Votes ->
  Votes
discardExpiredVotes window =
  S.filter $ \Vote{voteForBlock = Block{slotNumber}} -> slotNumber `inWindow` window

inWindow :: Ord a => a -> (a, a) -> Bool
inWindow x (xmin, xmax) = xmin <= x && x <= xmax

eligibleForInclusion ::
  [Block Votes] ->
  Votes ->
  (Slot, Slot) ->
  Votes ->
  Votes
eligibleForInclusion recordedBlocks recordedVotes window candidateVotes =
  let
    checkCandidate vote@Vote{voteForBlock} =
      let
        windowOkay = slotNumber voteForBlock `inWindow` window
        notRecorded = vote `S.notMember` recordedVotes
        blockOnChain = signature voteForBlock `elem` fmap signature recordedBlocks
       in
        windowOkay && notRecorded && blockOnChain
   in
    S.filter checkCandidate candidateVotes
