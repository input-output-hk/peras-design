```agda
module Peras.SmallStep.Experiment.Types where
```
<!--
```agda
open import Peras.Chain using (Chain)

{-# FOREIGN GHC
import qualified Peras.SmallStep.Experiment.Types as G
#-}
```
-->
```agda
record NodeState : Set where
  constructor MkNodeState
  field preferredChain : Chain
open NodeState public

record NodeTransition (a : Set) : Set where
  constructor MkNodeTransition
  field output : a
        final : NodeState
open NodeTransition public
```
<!--
```agda
{-# COMPILE AGDA2HS NodeState #-}
{-# COMPILE AGDA2HS NodeTransition #-}
{-# COMPILE GHC NodeState = data G.NodeState (G.MkNodeState) #-}
{-# COMPILE GHC NodeTransition = data G.NodeTransition (G.MkNodeTransition) #-}
```
-->
