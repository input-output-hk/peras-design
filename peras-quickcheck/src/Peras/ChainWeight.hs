module Peras.ChainWeight where

import Peras.Chain (Chain)
import Peras.SmallStep.Experiment (nextState)
import Peras.SmallStep.Experiment.Types (NodeState (..), NodeTransition (..))

initial :: NodeState
initial = MkNodeState{preferredChain = mempty}

test :: Bool
test = output $ nextState mempty initial
