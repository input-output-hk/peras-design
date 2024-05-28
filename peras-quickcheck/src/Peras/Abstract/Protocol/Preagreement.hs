{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.Abstract.Protocol.Preagreement (
  preagreement,
) where

import Prelude hiding (round)

import Control.Concurrent.Class.MonadSTM (MonadSTM, TVar, readTVarIO)
import Control.Tracer (Tracer, traceWith)
import Peras.Abstract.Protocol.Trace (PerasLog (..))
import Peras.Abstract.Protocol.Types (PerasParams (..), PerasResult, PerasState (..), VotingWeight)
import Peras.Block (Block (MkBlock, slotNumber), Party (pid))
import Peras.Numbering (RoundNumber (getRoundNumber), SlotNumber (getSlotNumber))

-- | FIXME: This is a placeholder for the real preagreement algorithm.
preagreement ::
  MonadSTM m =>
  Tracer m PerasLog ->
  PerasParams ->
  Party ->
  TVar m PerasState ->
  RoundNumber ->
  m (PerasResult (Maybe (Block, VotingWeight)))
preagreement tracer MkPerasParams{..} party stateVar round =
  do
    MkPerasState{..} <- readTVarIO stateVar
    let tooNew MkBlock{slotNumber} = getSlotNumber slotNumber + perasL >= getRoundNumber round * perasU
    case dropWhile tooNew chainPref of
      block : _ -> do
        traceWith tracer $ PreagreementBlock (pid party) block 1
        pure $ pure (Just (block, 1)) -- FIXME: Compute correct weight based on stake distribution.
      _ -> do
        traceWith tracer $ PreagreementNone (pid party)
        pure $ pure Nothing
