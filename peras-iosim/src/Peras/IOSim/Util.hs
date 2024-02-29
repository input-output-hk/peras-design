module Peras.IOSim.Util (
  votesInBlock,
) where

import Peras.Block (Block)
import Peras.Chain (Vote (blockHash))
import Peras.IOSim.Hash (hashBlock)
import Peras.IOSim.Types (Votes)

import qualified Data.Map as M

votesInBlock ::
  Block ->
  Votes ->
  Votes
votesInBlock block = M.filter $ (== hashBlock block) . blockHash
