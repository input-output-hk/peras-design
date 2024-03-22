{-# LANGUAGE RecordWildCards #-}

-- FIXME: Migrate to Agda.

module Peras.IOSim.Hash (
  BlockHash,
  BodyHash,
  ChainHash,
  VoteHash,
  castHash,
  genesisHash,
  hashBlock,
  hashBody,
  hashChain,
  hashTip,
  hashVote,
) where

import Peras.Block as Block (Block, BlockBody (blockHash), Tx)
import Peras.Chain as Chain (Vote (signature))
import Peras.Crypto as Crypto (Hash (..), Hashable (hash), Signature (bytes))

type BlockHash = Hash Block

hashBlock :: Block -> BlockHash
hashBlock = hash

genesisHash :: BlockHash
genesisHash = Hash mempty

hashTip :: [Block] -> BlockHash
hashTip [] = genesisHash
hashTip (block : _) = hashBlock block

type BodyHash = Hash [Tx]

type VoteHash = Hash Vote

hashVote :: Vote -> VoteHash
hashVote = Crypto.Hash . Crypto.bytes . Chain.signature

hashBody :: BlockBody -> BodyHash
hashBody = Block.blockHash

type ChainHash = Hash [Block]

hashChain :: [Block] -> ChainHash
hashChain [] = Hash . hashBytes $ genesisHash
hashChain (block : _) = Hash . hashBytes $ hashBlock block

castHash :: Hash a -> Hash b
castHash Hash{..} = Hash{..}
