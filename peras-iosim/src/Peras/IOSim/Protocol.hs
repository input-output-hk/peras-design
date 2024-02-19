{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.Protocol (
  newChain,
  nextSlot,
) where

import Control.Lens (use, uses, (.=))
import Control.Monad (replicateM)
import Control.Monad.Random (MonadRandom (getRandom, getRandomR))
import Control.Monad.State (MonadState)
import Data.Default (Default (def))
import Data.Function (on)
import Peras.Block (Block (Block), Slot)
import Peras.Chain (Chain (..))
import Peras.Crypto (Hash (Hash), LeadershipProof (LeadershipProof), Signature (Signature))
import Peras.IOSim.Node.Types (NodeState, owner, preferredChain, slot, slotLeader, stake)
import Peras.IOSim.Protocol.Types (Protocol (..))
import Peras.IOSim.Types (Coin, Votes)
import Peras.Message (Message (NewChain))

import qualified Data.ByteString as BS

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
nextSlot PseudoPeras{} _ _ = error "Pseudo-Peras protocol is not yet implemented."
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
newChain PseudoPeras{} _ = error "Pseudo-Peras protocol is not yet implemented."
newChain OuroborosPraos{} _ = error "Ouroboros-Praos protocol is not yet implemented."
newChain OuroborosGenesis{} _ = error "Ouroboros-Genesis protocol is not yet implemented."
newChain OuroborosPeras{} _ = error "Ouroboros-Peras protocol is not yet implemented."

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
  Protocol ->
  Coin ->
  Coin ->
  m Bool
isCommitteeMember PseudoPraos{} _ _ = pure False
isCommitteeMember PseudoPeras{..} total staked =
  let p = 1 - (1 - pCommitteeLottery) ** (fromIntegral staked / fromIntegral total)
   in (<= p) <$> getRandomR (0, 1)
isCommitteeMember OuroborosPraos{} _ _ = error "Ouroboros-Praos protocol is not yet implemented."
isCommitteeMember OuroborosGenesis{} _ _ = error "Ouroboros-Genesis protocol is not yet implemented."
isCommitteeMember OuroborosPeras{} _ _ = error "Ouroboros-Peras protocol is not yet implemented."
