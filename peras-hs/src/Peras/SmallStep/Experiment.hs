module Peras.SmallStep.Experiment where

import MAlonzo.Code.Peras.SmallStep.Experiment.Impl as M
import Peras.Chain (Chain)
import Peras.SmallStep.Experiment.Types (NodeState, NodeTransition)

nextState :: Chain -> NodeState -> NodeTransition Bool
nextState = M.nodeTransition
