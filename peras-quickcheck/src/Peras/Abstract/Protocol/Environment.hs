{-# LANGUAGE ScopedTypeVariables #-}

module Peras.Abstract.Protocol.Environment where

import Control.Concurrent.Class.MonadSTM (MonadSTM, TVar, atomically, newTVarIO, readTVar, writeTVar)
import qualified Data.Set as Set
import Peras.Abstract.Protocol.Crypto (createLeadershipProof, createSignedBlock, mkParty)
import Peras.Abstract.Protocol.Diffusion (Diffuser (..), defaultDiffuser)
import Peras.Abstract.Protocol.Types (genesisChain, mkParentBlock)
import Peras.Block (Party)
import Peras.Chain (Chain)
import Peras.Crypto (Hashable (..))
import Peras.Numbering (SlotNumber)

anotherParty :: Party
anotherParty = mkParty 43 [20] []

simpleScenario :: MonadSTM m => TVar m Chain -> SlotNumber -> m Diffuser
simpleScenario chain slotNumber =
  if slotNumber `mod` 20 == 0
    then do
      newChain <- atomically $ do
        currentChain :: Chain <- readTVar chain
        let parentBlock = mkParentBlock currentChain
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
      pure $ MkDiffuser{pendingChains = Set.singleton newChain, pendingVotes = mempty}
    else pure defaultDiffuser

mkSimpleScenario :: MonadSTM m => m (SlotNumber -> m Diffuser)
mkSimpleScenario = do
  chain <- newTVarIO genesisChain
  pure $ simpleScenario chain
