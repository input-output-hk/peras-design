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

nextState : Signal → NodeState → NodeTransition Response
nextState = signalImpl

propNeverShortens : NodeState → NodeState → Bool
propNeverShortens initial final = length (preferredChain initial) <= length (preferredChain final)
```
<!--
```agda
{-# FOREIGN AGDA2HS
nextState :: Signal -> NodeState -> NodeTransition Response
nextState = M.signalImpl
#-}
{-# COMPILE AGDA2HS propNeverShortens #-}
{-# COMPILE GHC nextState as nextState #-}
{-# COMPILE GHC propNeverShortens as propNeverShortens #-}
```
-->
```agda



```
