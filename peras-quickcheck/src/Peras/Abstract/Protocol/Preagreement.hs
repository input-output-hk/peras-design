{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.Abstract.Protocol.Preagreement (
  Preagreement,
  preagreement,
) where

import Prelude hiding (round)

import Control.Concurrent.Class.MonadSTM (MonadSTM, readTVarIO)
import Peras.Abstract.Protocol.Types (PerasParams (..), PerasState (..), Preagreement)
import Peras.Block (Block (MkBlock, slotNumber))
import Peras.Numbering (RoundNumber (getRoundNumber), SlotNumber (getSlotNumber))

-- | FIXME: This is a placeholder for the real preagreement algorithm.
preagreement :: MonadSTM m => Preagreement m
preagreement MkPerasParams{..} _party stateVar round =
  do
    MkPerasState{..} <- readTVarIO stateVar
    let tooNew MkBlock{slotNumber} = getSlotNumber slotNumber + perasL >= getRoundNumber round * perasU
    pure . pure $
      case dropWhile tooNew chainPref of
        block : _ -> Just (block, 1) -- FIXME: Compute correct weight based on stake distribution.
        _ -> Nothing
