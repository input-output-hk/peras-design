```agda
module Peras.SmallStep.Experiment where
```
<!--
```agda
open import Haskell.Prelude
open import Peras.Chain using (Chain)
open import Peras.SmallStep.Experiment.Impl
open import Peras.SmallStep.Experiment.Types

{-# FOREIGN AGDA2HS
import Peras.Chain (Chain)
import Peras.SmallStep.Experiment.Types
import MAlonzo.Code.Peras.SmallStep.Experiment.Impl as M
#-}
```
-->
```agda
mkResponse : (a → Response) → NodeTransition a → NodeTransition Response
mkResponse f (MkNodeTransition x state) = MkNodeTransition (f x) state

nodeTransition' : Chain → NodeState → NodeTransition Bool
nodeTransition' = nodeTransition

nextState : Signal → NodeState → NodeTransition Response
nextState (NewChain chain) = mkResponse ChainAdopted ∘ nodeTransition' chain
nextState ReportPreference = mkResponse ChainReported ∘ getPreferredChain
```
<!--
```agda
{-# COMPILE AGDA2HS mkResponse #-}
{-# FOREIGN AGDA2HS
nodeTransition' :: Chain -> NodeState -> NodeTransition Bool
nodeTransition' = M.nodeTransition
#-}
{-# COMPILE AGDA2HS nextState #-}
```
-->
```agda



```
