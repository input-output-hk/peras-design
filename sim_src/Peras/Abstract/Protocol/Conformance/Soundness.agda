
module Peras.Abstract.Protocol.Conformance.Soundness where

open import Haskell.Prelude
open import Data.Nat.Properties using (_≟_)
open import Data.Maybe using (maybe′)
open import Relation.Nullary.Decidable using (Dec; yes; no)

open import Peras.Block
open import Peras.Chain
open import Peras.Crypto
open import Peras.Numbering
open import Peras.Params
open import Prelude.AssocList
open import Prelude.DecEq using (DecEq)
import Peras.SmallStep as SmallStep

open import Peras.Abstract.Protocol.Params
open import Peras.Abstract.Protocol.Conformance.Model

module _ ⦃ _ : Hashable Block ⦄
         ⦃ _ : Hashable (List Tx) ⦄
         ⦃ params     : Params ⦄
         ⦃ network    : Network ⦄
         ⦃ postulates : Postulates ⦄
         {T : Set} {blockTree : SmallStep.TreeType T}
         {S : Set} {adversarialState₀ : S}
         {txSelection : SlotNumber → PartyId → List Tx}
         {parties : Parties} -- TODO: use parties from blockTrees
    where

  open SmallStep.Semantics {T} {blockTree} {S} {adversarialState₀} {txSelection} {parties}
  open SmallStep.TreeType blockTree

  buildChains : List Block → List Chain
  buildChains bs = {!!}
    -- Some juggling required to assemble the chains from the list of blocks.

  modelParams : PerasParams
  modelParams = record
    { perasU = U
    ; perasA = A
    ; perasR = R
    ; perasL = L
    ; perasτ = τ
    ; perasB = B
    ; perasT = 0      -- TODO: Missing from Params
    ; perasΔ = Δ
    }
    where
      open Params params
      open Network network

  modelState : State → NodeModel
  modelState s = record
    { clock        = State.clock s
    ; protocol     = modelParams
    ; allChains    = maybe′ (buildChains ∘ allBlocks) [] (State.blockTrees s ⁉ sutId)
    ; allVotes     = maybe′ votes                     [] (State.blockTrees s ⁉ sutId)
    ; allSeenCerts = maybe′ certs                     [] (State.blockTrees s ⁉ sutId)
    }

  sutVotesInStep : ∀ {s₀ s₁} → s₀ ↝ s₁ → List (SlotNumber × Vote)
  sutVotesInStep (Fetch _) = []
  sutVotesInStep {s₀ = s₀} (CreateVote _ (honest {p} {t} {M} {π} {σ} _ _ _ _ _)) =
    case p ≟ sutId of λ where
      (yes _) → (State.clock s₀ , createVote (State.clock M) p π σ t) ∷ []
      (no _)  → []
  sutVotesInStep (CreateBlock _ _) = []
  sutVotesInStep (NextSlot _ _) = []
  sutVotesInStep (NextSlotNewRound _ _ _) = []

  sutVotesInTrace : ∀ {s₀ s₁} → s₀ ↝⋆ s₁ → List (SlotNumber × Vote)
  sutVotesInTrace ∎              = []
  sutVotesInTrace (step ↣ trace) = sutVotesInStep step ++ sutVotesInTrace trace

  record Invariant (s : State) : Set where

  record Soundness (s₀ : State) (ms₁ : NodeModel) (vs : List (SlotNumber × Vote)) : Set where
    field
      s₁          : State
      invariant₀  : Invariant s₀
      invariant₁  : Invariant s₁
      trace       : s₀ ↝⋆ s₁
      s₁-agrees   : modelState s₁ ≡ ms₁
      votes-agree : sutVotesInTrace trace ≡ vs

  soundness : ∀ {ms₁ vs} (s₀ : State) (a : EnvAction)
            → Invariant s₀
            → transition (modelState s₀) a ≡ Just (vs , ms₁)
            → Soundness s₀ ms₁ (map (State.clock s₀ ,_) vs)
  soundness s₀ Tick inv prf = {!!}
  soundness s₀ (NewChain x) inv prf = {!!}
  soundness s₀ (NewVote vote) inv refl = record
    { s₁          = {!!}
    ; invariant₀  = inv
    ; invariant₁  = {!!}
    ; trace       = CreateVote {h = Honest {p = Vote.creatorId vote}}
                               {!!} -- Fetched s₀ (needs to go in the invariant?)
                               (honest {!!} {!!} {!!} {!!} {!!})
                                    -- TODO: here we need preconditions on the vote
                  ↣ ∎
    ; s₁-agrees   = {!!}
    ; votes-agree = {!!}
    }
