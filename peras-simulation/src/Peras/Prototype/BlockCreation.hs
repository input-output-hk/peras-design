{-# LANGUAGE RecordWildCards #-}

module Peras.Prototype.BlockCreation where

import Prelude hiding (round)

import Control.Concurrent.Class.MonadSTM (MonadSTM (..), atomically)
import Control.Monad (when)
import Control.Monad.Except (ExceptT (ExceptT), runExceptT)
import Control.Monad.State (lift)
import Control.Tracer (Tracer, traceWith)
import Peras.Block (Certificate (round), Party (pid), Tx)
import Peras.Crypto (Hashable (hash))
import Peras.Numbering (SlotNumber)
import Peras.Orphans ()
import Peras.Prototype.Crypto (createLeadershipProof, createSignedBlock, isSlotLeader)
import Peras.Prototype.Trace (PerasLog (..))
import Peras.Prototype.Types (DiffuseChain, PerasParams (..), PerasResult, PerasState (..), hashTip, inRound)

import qualified Data.Map as Map (keys)
import qualified Data.Set as Set (insert, singleton)

-- Whenever party P is slot leader in a slot s, belonging to some round r.
blockCreation ::
  MonadSTM m =>
  Tracer m PerasLog ->
  PerasParams ->
  Party ->
  TVar m PerasState ->
  SlotNumber ->
  [Tx] ->
  DiffuseChain m ->
  m (PerasResult ())
blockCreation tracer protocol@MkPerasParams{..} party stateVar s payload diffuseChain =
  runExceptT $
    when (isSlotLeader party s) $
      do
        MkPerasState{..} <- lift $ readTVarIO stateVar
        -- 1. Create a new block.
        lproof <- ExceptT $ createLeadershipProof s (Set.singleton party)
        let r = inRound s protocol
            parent = hashTip chainPref
            -- There is no round-(r-2) certificate in Certs, and
            bc1a = all ((/= r) . (2 +) . round) $ Map.keys certs
            -- r - round(cert') <= A, and
            bc1b = r <= round certPrime + fromIntegral perasA
            -- round(cert') > round(cert*),
            bc1c = round certPrime > round certStar
            -- then set cert to cert'.
            certificate =
              if bc1a && bc1b && bc1c
                then Just certPrime
                else Nothing
        block <- ExceptT $ createSignedBlock party s parent certificate lproof (hash payload)
        lift . traceWith tracer $ ForgingLogic (pid party) bc1a bc1b bc1c block
        -- 2. Extend Cpref by B, add the new Cpref to C and diffuse it.
        let chain' = block : chainPref
        lift . traceWith tracer $ NewChainPref (pid party) chain'
        lift . atomically $ modifyTVar stateVar $ \state -> state{chainPref = chain', chains = Set.insert chain' chains}
        ExceptT $ diffuseChain s chain'
