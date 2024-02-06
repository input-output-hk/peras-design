{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}

module Peras.RandomForks.Chain (
  blocks
, chainLength
, extendChain
, mkBlock
) where

import Peras.RandomForks.Types (Block(..), Chain(..), PeerName, Slot)
import System.Random.Stateful (StatefulGen(uniformShortByteString))

mkBlock
  :: StatefulGen g m
  => g
  -> PeerName
  -> Slot
  -> m Block
mkBlock gen name slot = Block name slot <$> uniformShortByteString 8 gen

blocks :: Chain -> [Block]
blocks = \case
  Genesis -> []
  Chain {block, prev} -> block : blocks prev

chainLength
  :: Chain
  -> Int
chainLength = \case
  Genesis -> 0
  Chain{prev} -> 1 + chainLength prev

extendChain
  :: Block
  -> Chain
  -> Chain
extendChain = Chain

