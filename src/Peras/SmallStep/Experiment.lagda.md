```agda
module Peras.SmallStep.Experiment where
```
<!--
```agda
open import Haskell.Prelude
open import Peras.Chain using (Chain)
open import Peras.SmallStep.Experiment.Impl using (nodeTransition)
open import Peras.SmallStep.Experiment.Types using (NodeState; NodeTransition)

{-# FOREIGN AGDA2HS
import Peras.Chain (Chain)
import Peras.SmallStep.Experiment.Types (NodeState, NodeTransition)
import MAlonzo.Code.Peras.SmallStep.Experiment.Impl as M
#-}
```
-->
```agda
nextState : Chain → NodeState → NodeTransition Bool
nextState = nodeTransition
```
<!--
```agda
{-# FOREIGN AGDA2HS
nextState :: Chain -> NodeState -> NodeTransition Bool
nextState = M.nodeTransition
#-}
```
-->
