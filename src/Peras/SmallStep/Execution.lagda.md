```agda
module Peras.SmallStep.Execution where
```

<!--
```agda
open import Data.Fin using (Fin; zero; suc) renaming (pred to decr)
open import Data.List using (List; _∷_; [])
open import Data.List.Relation.Unary.All using (All)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂; curry; uncurry)
open import Data.Maybe using (just; nothing)
open import Function using (_∘_; id; _$_; flip)

open import Peras.Chain
open import Peras.Crypto
open import Peras.Block
open import Peras.Params
open import Peras.SmallStep
open TreeType

open import Data.Tree.AVL.Map PartyIdO as M using (Map; lookup; insert; empty; fromList)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym; subst; trans)
```
-->

```agda
module _ {block₀ : Block} {cert₀ : Certificate}
         (IsCommitteeMember : PartyId → RoundNumber → MembershipProof → Set)
         (IsVoteSignature : Vote → Signature → Set)
         (IsSlotLeader : PartyId → Slot → LeadershipProof → Set)
         (IsBlockSignature : Block → Signature → Set)
         ⦃ _ : Hashable Block ⦄
         ⦃ _ : Hashable (List Tx) ⦄
         ⦃ _ : Params ⦄
         where

  open Hashable ⦃...⦄
  open Params ⦃...⦄

  module _ {A : Set}
           (blockTree : TreeType A)
           {AdversarialState : Set}
           (adversarialState₀ : AdversarialState)
           (txSelection : Slot → PartyId → List Tx)
           where

    private
      p₁ p₂ : PartyId
      p₁ = 1
      p₂ = 2

      parties : Parties
      parties = (p₁ , Honest) ∷ (p₂ , Honest) ∷ []

      LocalState′ = Stateˡ {block₀} {cert₀} {IsCommitteeMember} {IsVoteSignature} {IsSlotLeader} {IsBlockSignature} {A} {blockTree} {AdversarialState} {adversarialState₀} {txSelection} {parties}
      GlobalState = Stateᵍ {block₀} {cert₀} {IsCommitteeMember} {IsVoteSignature} {IsSlotLeader} {IsBlockSignature} {A} {blockTree} {AdversarialState} {adversarialState₀} {txSelection} {parties}

      start : Map LocalState′
      start = fromList (
          (p₁ , ⟪ tree₀ blockTree ⟫)
        ∷ (p₂ , ⟪ tree₀ blockTree ⟫)
        ∷ [])

      initialState : GlobalState
      initialState = ⟦ 0 , start , [] , [] , adversarialState₀ ⟧

      postulate
        prf : LeadershipProof
        sig : Signature

      txs : List Tx
      txs = txSelection 1 p₁

      b : Block
      b = record
            { slotNumber = 1
            ; creatorId = p₁
            ; parentBlock = hash $ tipBest blockTree 1 (tree₀ blockTree)
            ; certificate = nothing
            ; leadershipProof = prf
            ; bodyHash = blockHash
                record { blockHash = hash txs
                       ; payload = txs
                       }
            ; signature = sig
            }

      postulate
        isSlotLeader : IsSlotLeader p₁ 1 prf
        isBlockSignature : IsBlockSignature b sig

      end : Map LocalState′
      end = fromList (
          (p₁ , ⟪ extendTree blockTree (tree₀ blockTree) b ⟫)
        ∷ (p₂ , ⟪ tree₀ blockTree ⟫)
        ∷ [])

      m : Message
      m = BlockMsg b

      e₁ e₂ : Envelope
      e₁ = ⦅ p₁ , Honest , m , zero ⦆
      e₂ = ⦅ p₂ , Honest , m , zero ⦆

      finalState : GlobalState
      finalState = ⟦ 1 , end , e₂ ∷ [] , m ∷ [] , adversarialState₀ ⟧

      intermediaryState : GlobalState
      intermediaryState = ⟦ 1 , start , [] , [] , adversarialState₀ ⟧

      s₁ : initialState ↝ intermediaryState
      s₁ = NextSlot All.[]

      s₂ : intermediaryState ↝ finalState
      s₂ = CreateBlock (honest refl refl isBlockSignature isSlotLeader)

      _ : initialState ↝⋆ finalState
      _ = initialState ↝⟨ s₁ ⟩ (intermediaryState ↝⟨ s₂ ⟩ (finalState ∎))
```
