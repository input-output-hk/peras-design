{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.Prototype.Preagreement (
  preagreement,
) where

import Control.Concurrent.Class.MonadSTM (MonadSTM, TVar, readTVarIO)
import Control.Tracer (Tracer, traceWith)
import Peras.Block (Block (MkBlock, slotNumber), Party (pid))
import Peras.Numbering (RoundNumber)
import Peras.Prototype.Trace (PerasLog (..))
import Peras.Prototype.Types (PerasParams (..), PerasResult, PerasState (..), VotingWeight)
import Prelude hiding (round)

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
    MkPerasState{chainPref} <- readTVarIO stateVar
    -- Let B be the youngest block at least L slots old on Cpref.
    let oldEnough MkBlock{slotNumber} = fromIntegral slotNumber + perasL <= fromIntegral round * perasU
    case dropWhile (not . oldEnough) chainPref of
      block : _ -> do
        -- FIXME: Compute correct weight based on stake distribution.
        let votingWeight = 1
        traceWith tracer $ PreagreementBlock (pid party) block votingWeight
        pure $ pure (Just (block, votingWeight))
      _ -> do
        traceWith tracer $ PreagreementNone (pid party)
        pure $ pure Nothing
