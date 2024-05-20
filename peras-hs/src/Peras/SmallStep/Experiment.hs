module Peras.SmallStep.Experiment where

import MAlonzo.Code.Peras.SmallStep.Experiment.Impl as M
import Peras.Chain (Chain)
import Peras.SmallStep.Experiment.Types

mkResponse ::
  (a -> Response) -> NodeTransition a -> NodeTransition Response
mkResponse f (MkNodeTransition x state) =
  MkNodeTransition (f x) state

nextState :: Signal -> NodeState -> NodeTransition Response
nextState (NewChain chain) =
  mkResponse ChainAdopted . nodeTransition' chain
nextState ReportPreference =
  mkResponse ChainReported . getPreferredChain

nodeTransition' :: Chain -> NodeState -> NodeTransition Bool
nodeTransition' = M.nodeTransition
