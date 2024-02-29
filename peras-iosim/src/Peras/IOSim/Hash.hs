-- FIXME: Migrate to Agda.

module Peras.IOSim.Hash (
  hashBlock,
  hashVote,
  genesisHash,
) where

import Peras.Block as Block
import Peras.Chain as Chain
import Peras.Crypto as Crypto

hashBlock :: Block.Block -> Crypto.Hash
hashBlock = Crypto.Hash . Crypto.bytes . Block.signature

hashVote :: Chain.Vote msg -> Crypto.Hash
hashVote = Crypto.Hash . Crypto.bytes . Chain.signature

genesisHash :: Hash
genesisHash = Hash mempty
