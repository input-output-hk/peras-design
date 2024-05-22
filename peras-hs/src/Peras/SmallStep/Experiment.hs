module Peras.SmallStep.Experiment where

import MAlonzo.Code.Peras.SmallStep.Experiment.Impl as M
import Peras.Chain (Chain)
import Peras.SmallStep.Experiment.Types

propNeverShortens :: NodeState -> NodeState -> Bool
propNeverShortens initial final =
  length (preferredChain initial) <= length (preferredChain final)

nextState :: Signal -> NodeState -> NodeTransition Response
nextState = M.signalImpl
