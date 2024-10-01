{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.Prototype.BlockSelection (
  selectBlock,
) where

import Control.Concurrent.Class.MonadSTM (MonadSTM, TVar, readTVarIO)
import Control.Tracer (Tracer, traceWith)
import Peras.Block (Block (..), Party (pid))
import Peras.Numbering (RoundNumber)
import Peras.Prototype.Trace (PerasLog (..))
import Peras.Prototype.Types (PerasParams (..), PerasResult, PerasState (..), VotingWeight)
import Prelude hiding (round)

selectBlock ::
  MonadSTM m =>
  Tracer m PerasLog ->
  PerasParams ->
  Party ->
  TVar m PerasState ->
  RoundNumber ->
  m (PerasResult (Maybe (Block, VotingWeight)))
selectBlock tracer MkPerasParams{..} party stateVar round =
  do
    MkPerasState{chainPref} <- readTVarIO stateVar
    -- Let B be the youngest block at least L slots old on Cpref.
    let oldEnough MkBlock{slotNumber} =
          let r = fromIntegral round * perasU
              s = fromIntegral slotNumber + perasL
           in s <= r
    case dropWhile (not . oldEnough) chainPref of
      block : _ -> do
        -- FIXME: Compute correct weight based on stake distribution.
        let votingWeight = 1
        traceWith tracer $ SelectedBlock (pid party) block votingWeight
        pure $ pure (Just (block, votingWeight))
      _ -> do
        traceWith tracer $ NoBlockSelected (pid party)
        pure $ pure Nothing
