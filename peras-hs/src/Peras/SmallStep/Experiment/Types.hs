module Peras.SmallStep.Experiment.Types where

import Peras.Chain (Chain)

data NodeState = MkNodeState {preferredChain :: Chain}

data NodeTransition a = MkNodeTransition
  { output :: a
  , final :: NodeState
  }
