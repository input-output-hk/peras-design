```agda
module Peras.SmallStep.Experiment.Types where
```
<!--
```agda
open import Haskell.Prelude using (Bool)
open import Peras.Chain using (Chain)

{-# FOREIGN AGDA2HS
{-# LANGUAGE DeriveGeneric #-}
import GHC.Generics (Generic)
import Peras.Orphans ()
#-}

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

data Signal : Set where
  NewChain : Chain → Signal
  ReportPreference : Signal
open Signal public

data Response : Set where
  ChainAdopted : Bool → Response
  ChainReported : Chain → Response
open Response public
```
<!--
```agda
{-# COMPILE AGDA2HS NodeState newtype deriving (Eq, Generic, Show) #-}
{-# COMPILE AGDA2HS NodeTransition deriving (Eq, Generic, Show) #-}
{-# COMPILE AGDA2HS Signal deriving (Eq, Generic, Show) #-}
{-# COMPILE AGDA2HS Response deriving (Eq, Generic, Show) #-}
{-# COMPILE GHC NodeState = data G.NodeState (G.MkNodeState) #-}
{-# COMPILE GHC NodeTransition = data G.NodeTransition (G.MkNodeTransition) #-}
{-# COMPILE GHC Signal = data G.Signal (G.NewChain | G.ReportPreference) #-}
{-# COMPILE GHC Response = data G.Response (G.ChainAdopted | G.ChainReported) #-}
```
-->
