```agda
module Peras.SmallStep.Execution where
```

<!--
```agda
open import Data.Fin using (Fin; zero; suc) renaming (pred to decr)
open import Data.List using (List; _∷_; [])
open import Data.List.Relation.Unary.Any using (Any; here)
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

      initialState : GlobalState
      initialState = ⟦ 0 , initialMap , [] , [] , adversarialState₀ ⟧
        where
          initialMap = fromList (
              (p₁ , ⟪ tree₀ blockTree ⟫)
            ∷ (p₂ , ⟪ tree₀ blockTree ⟫)
            ∷ [])

      postulate
        prf : LeadershipProof
        sig : Signature

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
        where
          txs = txSelection 1 p₁

      finalState : GlobalState
      finalState = ⟦ 2 , finalMap , [] , BlockMsg b ∷ [] , adversarialState₀ ⟧
        where
          finalMap = fromList (
              (p₁ , ⟪ extendTree blockTree (tree₀ blockTree) b ⟫)
            ∷ (p₂ , ⟪ extendTree blockTree (tree₀ blockTree) b ⟫)
            ∷ [])

      postulate
        isSlotLeader : IsSlotLeader p₁ 1 prf
        isBlockSignature : IsBlockSignature b sig

      _ : initialState ↝⋆ finalState
      _ =    NextSlot All.[]
          ∷′ CreateBlock (honest refl refl isBlockSignature isSlotLeader)
          ∷′ Deliver (honest refl (here refl) BlockReceived)
          ∷′ NextSlot All.[]
          ∷′ []′
```
