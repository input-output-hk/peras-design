```agda
module Peras.SmallStep.Experiment.Impl where

open import Haskell.Prelude
open import Peras.Block using (Block; signature)
open import Peras.Crypto using (Hashable; MkHash; bytesS)
open import Peras.Params using (Params)
open import Peras.SmallStep.Experiment.Types

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

newChain : Chain → NodeState → NodeTransition Bool
newChain candidate state =
  let certs = []
  in if ∥ candidate ∥ certs > ∥ preferredChain state ∥ certs
        then MkNodeTransition True $ record state {preferredChain = candidate}
        else MkNodeTransition False state

getChain : NodeState → NodeTransition Chain
getChain state = MkNodeTransition (preferredChain state) state

mkResponse : (a → Response) → NodeTransition a → NodeTransition Response
mkResponse f (MkNodeTransition x state) = MkNodeTransition (f x) state

transitionImpl : Act → NodeState → NodeTransition Response
transitionImpl (NewChain chain) = mkResponse BoolResponse ∘ newChain chain

observeImpl : Query → NodeState → Response
observeImpl QueryChain = ChainResponse ∘ preferredChain
observeImpl QueryWeight = NatResponse ∘ foldr (const $ _+_ 1) 0 ∘ preferredChain

signalImpl : Signal → NodeState → NodeTransition Response
signalImpl (Transition act) state = transitionImpl act state
signalImpl (Observe query) state = MkNodeTransition (observeImpl query state) state

neverShortens? : List Act → NodeState → Bool
neverShortens? signals state =
  let certs = []
      state' = foldl (flip $ fmap final ∘ transitionImpl) state signals
  in ∥ preferredChain state' ∥ certs >= ∥ preferredChain state ∥ certs
```
<!--
```agda
{-# COMPILE GHC signalImpl as signalImpl #-}
{-# COMPILE GHC neverShortens? as neverShortensDec #-}
```
-->
