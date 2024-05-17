module Peras.SmallStep.Experiment.Impl where

open import Haskell.Prelude
open import Peras.Block using (Block; signature)
open import Peras.Crypto using (Hashable; MkHash; bytesS)
open import Peras.Params using (Params)
open import Peras.SmallStep.Experiment.Types using (NodeState; preferredChain; NodeTransition; MkNodeTransition)

open Hashable ⦃...⦄

instance
  iBlockHashable : Hashable Block
  iBlockHashable .hash = MkHash ∘ bytesS ∘ signature

instance
  defaultParams : Params
  defaultParams =
    record
    {
      T = 20
    ; K = 120
    ; R = 120
    ; L = 120
    ; A = 120
    ; τ = 20
    ; B = 1
    ; W = 600
    }

open import Peras.Chain using (Chain; ∥_∥_)

nodeTransition : Chain → NodeState → NodeTransition Bool
nodeTransition candidate state =
  if ∥ candidate ∥ [] > ∥ preferredChain state ∥ []
      then MkNodeTransition True $ record state {preferredChain = candidate}
      else MkNodeTransition False state

{-# COMPILE GHC nodeTransition as nodeTransition #-}