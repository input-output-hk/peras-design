```agda
module Peras.SmallStep.Experiment.Types where
```
<!--
```agda
open import Data.Nat using (ℕ)
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

data Act : Set where
  NewChain : Chain → Act
open Act public

data Query : Set where
  QueryChain : Query
  QueryWeight : Query
open Query public

data Signal : Set where
  Transition : Act → Signal
  Observe : Query → Signal
open Signal public

data Response : Set where
  UnitResponse : Response
  BoolResponse : Bool → Response
  NatResponse : ℕ → Response
  ChainResponse : Chain → Response
open Response public
```
<!--
```agda
{-# COMPILE AGDA2HS NodeState newtype deriving (Eq, Generic, Show) #-}
{-# COMPILE AGDA2HS NodeTransition deriving (Eq, Generic, Show) #-}
{-# COMPILE AGDA2HS Act newtype deriving (Eq, Generic, Show) #-}
{-# COMPILE AGDA2HS Query deriving (Eq, Generic, Show) #-}
{-# COMPILE AGDA2HS Signal deriving (Eq, Generic, Show) #-} 
{-# FOREIGN AGDA2HS
data Response =
    UnitResponse
  | BoolResponse Bool
  | NatResponse Integer
  | ChainResponse Chain
  deriving (Eq, Generic, Show)
#-}
{-# COMPILE GHC NodeState = data G.NodeState (G.MkNodeState) #-}
{-# COMPILE GHC NodeTransition = data G.NodeTransition (G.MkNodeTransition) #-}
{-# COMPILE GHC Act = data G.Act (G.NewChain) #-}
{-# COMPILE GHC Query = data G.Query (G.QueryChain | G.QueryWeight) #-}
{-# COMPILE GHC Signal = data G.Signal (G.Transition | G.Observe) #-}
{-# COMPILE GHC Response = data G.Response (G.UnitResponse | G.BoolResponse | G.NatResponse | G.ChainResponse) #-}
```
-->
