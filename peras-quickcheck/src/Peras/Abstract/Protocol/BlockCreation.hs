{-# LANGUAGE RecordWildCards #-}

module Peras.Abstract.Protocol.BlockCreation where

import Prelude hiding (round)

import Control.Concurrent.Class.MonadSTM (MonadSTM (..), atomically)
import Control.Monad (when)
import Control.Monad.Except (ExceptT (ExceptT), runExceptT)
import Control.Monad.State (lift)
import Peras.Abstract.Protocol.Crypto (createLeadershipProof, createSignedBlock, isSlotLeader)
import Peras.Abstract.Protocol.Types (BlockCreation, PerasParams (..), PerasState (..), hashTip)
import Peras.Block (Certificate (round))
import Peras.Crypto (Hashable (hash))
import Peras.Orphans ()

import qualified Data.Map as Map (keys)
import qualified Data.Set as Set (insert, singleton)

blockCreation :: MonadSTM m => BlockCreation m
blockCreation MkPerasParams{..} party stateVar s payload diffuseChain =
  runExceptT $
    when (isSlotLeader party s) $
      do
        MkPerasState{..} <- lift $ readTVarIO stateVar
        lproof <- ExceptT $ createLeadershipProof s (Set.singleton party)
        let r = fromIntegral $ fromIntegral s `div` perasU
            parent = hashTip chainPref
            bc1a = all ((/= r) . round) $ Map.keys certs
            bc1b = r <= round certPrime + fromIntegral perasA
            bc1c = round certPrime > round certStar
            certificate =
              if bc1a && bc1b && bc1c
                then Just certPrime
                else Nothing
        block <- ExceptT $ createSignedBlock party s parent certificate lproof (hash payload)
        let chain' = block : chainPref
        lift . atomically $ modifyTVar stateVar $ \state -> state{chainPref = chain', chains = Set.insert chain' chains}
        ExceptT $ diffuseChain chain'
