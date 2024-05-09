module Peras.QCD.Node.Preagreement where

import Peras.QCD.Node.Model (NodeState, currentSlot, peras)
import Peras.QCD.Protocol (ParamSymbol (L))
import Peras.QCD.State (use)
import Peras.QCD.Types (Block)

import Peras.QCD.Types.Instances ()

preagreement :: NodeState (Maybe Block)
preagreement =
  do
    l <- peras L
    now <- use currentSlot
    pure Nothing
