-- FIXME: Migrate to Agda.

module Peras.IOSim.Hash (
  hashBlock,
  hashVote,
  genesisHash,
  BlockHash,
  VoteHash,
  hashTip,
) where

import Peras.Block as Block
import Peras.Chain as Chain
import Peras.Crypto as Crypto

type BlockHash = Hash

hashBlock :: Block -> BlockHash
hashBlock = Crypto.Hash . Crypto.bytes . Block.signature

genesisHash :: BlockHash
genesisHash = Hash mempty

hashTip :: [Block] -> BlockHash
hashTip [] = genesisHash
hashTip (block : _) = hashBlock block

type VoteHash = Hash

hashVote :: Vote msg -> VoteHash
hashVote = Crypto.Hash . Crypto.bytes . Chain.signature
