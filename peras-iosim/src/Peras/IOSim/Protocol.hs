{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.Protocol (
  newChain,
  nextSlot,
) where

import Control.Lens ((&), (.~), (^.))
import Data.Bifunctor (first)
import Data.Default (Default (def))
import Peras.Block (Block (Block), Slot)
import Peras.Chain (Chain (..))
import Peras.Crypto (Hash (Hash), LeadershipProof (LeadershipProof), Signature (Signature))
import Peras.IOSim.Node.Types (NodeState, owner, preferredChain, slot, slotLeader, stake)
import Peras.IOSim.Protocol.Types (Protocol (..))
import Peras.IOSim.Simulate.Types (Parameters (..))
import Peras.IOSim.Types (Currency)
import Peras.Message (Message (NewChain))
import System.Random (RandomGen (..), genByteString, uniformR)

-- FIXME: We need an implementation of `MonadRandom` within `IOSim`.

nextSlot ::
  Default v =>
  RandomGen g =>
  g ->
  Parameters ->
  Protocol ->
  Slot ->
  NodeState v ->
  ((NodeState v, Maybe (Message v)), g)
nextSlot gen parameters PseudoPraos{..} slot' state =
  let (leader, gen') = isSlotLeader gen parameters activeSlotCoefficient $ state ^. stake
   in if leader
        then
          let (signature, gen'') = Signature `first` genByteString 6 gen'
              block = Block slot' (state ^. owner) (Hash mempty) def (LeadershipProof mempty) mempty signature
              chain = Cons block $ state ^. preferredChain
           in (
                ( state
                    & slot .~ slot'
                    & preferredChain .~ chain
                    & slotLeader .~ leader
                , Just $ NewChain chain
                )
              , gen''
              )
        else
          (
            ( state
                & slot .~ slot'
                & slotLeader .~ leader
            , Nothing
            )
          , gen'
          )
nextSlot _ _ PseudoPeras{} _ _ = error "Pseudo-Peras protocol is not yet implemented."
nextSlot _ _ OuroborosPraos{} _ _ = error "Ouroboros-Praos protocol is not yet implemented."
nextSlot _ _ OuroborosGenesis{} _ _ = error "Ouroboros-Genesis protocol is not yet implemented."
nextSlot _ _ OuroborosPeras{} _ _ = error "Ouroboros-Peras protocol is not yet implemented."

newChain ::
  RandomGen g =>
  g ->
  Parameters ->
  Protocol ->
  Chain v ->
  NodeState v ->
  ((NodeState v, Maybe (Message v)), g)
newChain gen _ PseudoPraos{} chain state =
  let length' Genesis = (0 :: Int)
      length' (Cons _ chain') = 1 + length' chain'
   in if length' chain > length' (state ^. preferredChain)
        then
          (
            ( state & preferredChain .~ chain
            , if False
                then Just $ NewChain chain -- FIXME: The chain propagates too quickly if we don't delay messages.
                else Nothing -- FIXME: The chain doesn't propagate quickly enough if we don't forward new chains.
            )
          , gen
          )
        else ((state, Nothing), gen)
newChain _ _ PseudoPeras{} _ _ = error "Pseudo-Peras protocol is not yet implemented."
newChain _ _ OuroborosPraos{} _ _ = error "Ouroboros-Praos protocol is not yet implemented."
newChain _ _ OuroborosGenesis{} _ _ = error "Ouroboros-Genesis protocol is not yet implemented."
newChain _ _ OuroborosPeras{} _ _ = error "Ouroboros-Peras protocol is not yet implemented."

isSlotLeader ::
  RandomGen g =>
  g ->
  Parameters ->
  Double ->
  Currency ->
  (Bool, g)
isSlotLeader gen Parameters{..} activeSlotCoefficient' currency =
  -- FIXME: This is just a crude approximation to the actual Praos leader-selection algorithm.
  let expectedStake = fromIntegral $ peerCount * maximumStake `div` 2
      pSlotLottery = 1 - (1 - activeSlotCoefficient') ** (1 / expectedStake)
      p = 1 - (1 - pSlotLottery) ^ currency
   in (<= p) `first` uniformR (0, 1) gen
