-- FIXME: Migrate to Agda.

module Peras.IOSim.Hash (
  BlockHash,
  BodyHash,
  VoteHash,
  genesisHash,
  hashBlock,
  hashBody,
  hashTip,
  hashVote,
) where

import Peras.Block as Block (Block (bodyHash), BlockBody (blockHash), Tx)
import Peras.Chain as Chain (Vote (signature))
import Peras.Crypto as Crypto (Hash (Hash), Signature (bytes))

type BlockHash = Hash [Tx]

hashBlock :: Block -> BlockHash
hashBlock = Block.bodyHash

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
