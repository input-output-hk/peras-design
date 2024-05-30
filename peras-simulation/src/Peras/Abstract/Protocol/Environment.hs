{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Peras.Abstract.Protocol.Environment where

import Control.Concurrent.Class.MonadSTM (MonadSTM, TVar, atomically, newTVarIO, readTVar, readTVarIO, writeTVar)
import Control.Monad (forM)
import Control.Monad.Except (ExceptT (..), runExceptT)
import Data.Either (partitionEithers)
import qualified Data.Set as Set
import Peras.Abstract.Protocol.Crypto (createLeadershipProof, createMembershipProof, createSignedBlock, createSignedVote, isSlotLeader, mkParty)
import Peras.Abstract.Protocol.Diffusion (Diffuser, defaultDiffuser, insertChains, insertVotes)
import Peras.Abstract.Protocol.Types (PerasParams (..), defaultParams, genesisChain, hashTip, inRound, perasL, perasU, systemStart)
import Peras.Block (Block, Party, slotNumber)
import Peras.Chain (Chain)
import Peras.Crypto (Hashable (..))
import Peras.Numbering (SlotNumber)
import Prelude hiding (round)

anotherParty :: Party
anotherParty = mkParty 43 [20, 40 .. 1000] []

-- | Describes the "Happy Path" scenario where there's a steady flow of blocks and votes forming a quorum.
simpleScenario :: MonadSTM m => TVar m Chain -> PerasParams -> SlotNumber -> m Diffuser
simpleScenario chain params@MkPerasParams{perasU, perasL} slotNumber =
  generateVotes >>= generateNewChain
 where
  generateNewChain diffuser
    | anotherParty `isSlotLeader` slotNumber = do
        newChain <- atomically $ do
          currentChain :: Chain <- readTVar chain
          let parentBlock = hashTip currentChain
              bodyHash = hash mempty
          leadershipProof <-
            either (error . show) id
              <$> createLeadershipProof slotNumber (Set.singleton anotherParty)
          block <-
            either (error . show) id
              <$> createSignedBlock anotherParty slotNumber parentBlock Nothing leadershipProof bodyHash
          let newChain = block : currentChain
          writeTVar chain newChain
          pure newChain
        pure $ insertChains systemStart (Set.singleton newChain) diffuser
    | otherwise = pure diffuser

  -- generate 10 votes every slot in a round
  generateVotes = do
    let round = inRound (fromIntegral slotNumber :: Integer) params
        slotInRound = fromIntegral slotNumber `mod` perasU
    blockToVoteFor <- blockBefore perasL (fromIntegral round * perasU) <$> readTVarIO chain
    case blockToVoteFor of
      Nothing -> pure $ defaultDiffuser 0
      Just block -> do
        let blockHash = hash block
        (_, votes) <-
          partitionEithers
            <$> forM
              [slotInRound * 10 .. (slotInRound + 1) * 10 - 1]
              ( \pid -> runExceptT $ do
                  let party = mkParty pid [] []
                  proof <- ExceptT $ createMembershipProof round (Set.singleton party)
                  ExceptT $ createSignedVote party round blockHash proof 1
              )
        pure $ insertVotes systemStart (Set.fromList votes) $ defaultDiffuser 0

blockBefore :: Integer -> Integer -> Chain -> Maybe Block
blockBefore cutoff slot = \case
  [] -> Nothing
  (b : bs)
    | fromIntegral (slotNumber b) + cutoff < slot -> Just b
    | otherwise -> blockBefore cutoff slot bs

mkSimpleScenario :: MonadSTM m => m (SlotNumber -> m Diffuser)
mkSimpleScenario = do
  chain <- newTVarIO genesisChain
  pure $ simpleScenario chain defaultParams
