{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.RandomForks.Chain (
  blocks
, chainLength
, chainWeight
, extendChain
, filterSlotRange
, mkBlock
) where

import Peras.RandomForks.Types (Block(..), Chain(..), PeerName, Slot)
import System.Random.Stateful (StatefulGen(uniformShortByteString))

import qualified Data.Set as S

mkBlock
  :: StatefulGen g m
  => g
  -> PeerName
  -> Slot
  -> m Block
mkBlock gen name slot = flip (Block name slot) mempty <$> uniformShortByteString 4 gen

blocks
  :: Chain
  -> [Block]
blocks = \case
  Genesis -> []
  Chain {block, prev} -> block : blocks prev

filterSlotRange 
  :: (Slot, Slot)
  -> Chain
  -> [Block]
filterSlotRange (minSlot, maxSlot) chain =
  filter (\Block{slot} -> minSlot <= slot && slot <= maxSlot) $ blocks chain

chainLength
  :: Chain
  -> Int
chainLength = \case
  Genesis -> 0
  Chain{prev} -> 1 + chainLength prev

chainWeight
  :: Double
  -> Chain
  -> Double
chainWeight _ Genesis = 0
chainWeight boost Chain{..} = 1 + boost * (fromIntegral . S.size $ votes block) + chainWeight boost prev

extendChain
  :: Block
  -> Chain
  -> Chain
extendChain = Chain
