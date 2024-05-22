{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.Abstract.Protocol.Preagreement (
  preagreement,
) where

import Control.Concurrent.STM.TVar (readTVarIO)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Peras.Abstract.Protocol.Types (PerasParams (..), PerasState (..), Preagreement)
import Peras.Block (Block (MkBlock, slotNumber))
import Peras.Numbering (RoundNumber (getRoundNumber), SlotNumber (getSlotNumber))
import Prelude hiding (round)

-- | FIXME: This is a placeholder for the real preagreement algorithm.
preagreement :: MonadIO m => Preagreement m
preagreement PerasParams{..} _party stateVar round =
  do
    PerasState{..} <- liftIO $ readTVarIO stateVar
    let oldEnough MkBlock{slotNumber} = getSlotNumber slotNumber + perasL <= getRoundNumber round * perasU
    pure . pure $
      case dropWhile oldEnough chainPref of
        [block] -> Just (block, 1) -- FIXME: Compute correct weight based on stake distribution.
        _ -> Nothing
