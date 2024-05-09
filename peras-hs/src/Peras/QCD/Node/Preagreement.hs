module Peras.QCD.Node.Preagreement where

import Numeric.Natural (Natural)
import Peras.QCD.Node.Model (NodeState, currentSlot, peras, preferredChain)
import Peras.QCD.Protocol (ParamSymbol (L))
import Peras.QCD.State (use)
import Peras.QCD.Types (Block (slot), Slot, chainBlocks)
import Peras.QCD.Util ((⇉))

import Peras.QCD.Types.Instances ()

preagreement :: NodeState (Maybe Block)
preagreement =
  do
    l <- peras L
    now <- use currentSlot
    ((use preferredChain ⇉ chainBlocks) ⇉ dropWhile (newerThan l now))
      ⇉ foundBlock
 where
  newerThan :: Natural -> Slot -> Block -> Bool
  newerThan l now block = slot block + l > now
  foundBlock :: [Block] -> Maybe Block
  foundBlock [] = Nothing
  foundBlock (block : _) = Just block
