```agda
module Peras.SmallStep.Execution where
```

<!--
```agda
open import Data.Fin using (Fin; zero; suc) renaming (pred to decr)
open import Data.List using (List; _∷_; [])
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All) renaming ([] to empty)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂; curry; uncurry)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (_+_; _*_)
open import Data.Nat.Properties using (+-identityˡ; +-identityʳ)
open import Function using (_∘_; id; _$_; flip)

open import Peras.Chain
open import Peras.Crypto hiding (isCommitteeMember)
open import Peras.Block
open import Peras.Numbering
open import Peras.Params
open import Peras.SmallStep renaming (_∷′_ to _↣_; []′ to ∎)

open import Data.Tree.AVL.Map PartyIdO as M using (Map; lookup; insert; fromList)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym; subst; trans)
```
-->

```agda
module _ {block₀}
         (IsCommitteeMember : PartyId → RoundNumber → MembershipProof → Set)
         (IsVoteSignature : Vote → Signature → Set)
         (IsSlotLeader : PartyId → SlotNumber → LeadershipProof → Set)
         (IsBlockSignature : Block → Signature → Set)
         ⦃ _ : Hashable Block ⦄
         ⦃ _ : Hashable (List Tx) ⦄
         where

  open Hashable ⦃...⦄

  cert₀ : Certificate
  cert₀ = MkCertificate (MkRoundNumber 0) (hash block₀)

  instance
    params : Params
    params = record
               { U = 2
               ; K = 1
               ; R = 1
               ; L = 1
               ; A = 1
               ; τ = 1
               ; B = 1
               ; W = 1
               }
  open Params

  module _ {T : Set} (blockTree : TreeType T)
           {S : Set} (adversarialState₀ : S)
           (txSelection : SlotNumber → PartyId → List Tx)
           where

    open TreeType blockTree

    private
```
This is a very simple example of the execution of the protocol in the small-step semantics. There are only 2 parties and both parties are honest. The first party is the slot leader in the first slot and creates a block. The block is then delivered to the second party. The second party receives the block and the protocol moves to the next slot.
```agda
      p₁ p₂ : PartyId
      p₁ = 1
      p₂ = 2

      parties : Parties
      parties = (p₁ , Honest) ∷ (p₂ , Honest) ∷ []

      GlobalState = State {block₀} {cert₀} {IsCommitteeMember} {IsVoteSignature} {IsSlotLeader} {IsBlockSignature} {T} {blockTree} {S} {adversarialState₀} {txSelection} {parties}
```
Initial state
```agda
      initialState : GlobalState
      initialState = ⟦ MkSlotNumber 0 , initialMap , [] , [] , adversarialState₀ ⟧
        where
          initialMap = fromList ((p₁ , tree₀) ∷ (p₂ , tree₀) ∷ [])
```
```agda
      postulate
        prf : LeadershipProof
        sig : Signature

      b : Block
      b = record
            { slotNumber = MkSlotNumber 1
            ; creatorId = p₁
            ; parentBlock = hash $ tipBest (MkSlotNumber 1) tree₀ -- TODO: hash $ tip block₀
            ; certificate = nothing
            ; leadershipProof = prf
            ; bodyHash = blockHash
                record { blockHash = hash txs
                       ; payload = txs
                       }
            ; signature = sig
            }
        where
          txs = txSelection (MkSlotNumber 1) p₁
```
```agda
      postulate
        prf' : MembershipProof
        sig' : Signature

      v : Vote
      v = record
            { votingRound = MkRoundNumber 1
            ; creatorId = p₁
            ; proofM = prf'
            ; blockHash = hash $ tipBest (MkSlotNumber 1) (extendTree tree₀ b) -- TODO: hash $ tip b
            ; signature = sig'
            }
```
Final state after the execution of all the steps
```agda
      finalState : GlobalState
      finalState = ⟦ MkSlotNumber 3 , finalMap , [] , VoteMsg v ∷ BlockMsg b ∷ [] , adversarialState₀ ⟧
        where
          finalMap = fromList (
              (p₁ , addVote (extendTree tree₀ b) v)
            ∷ (p₂ , addVote (extendTree tree₀ b) v)
            ∷ [])
```
```agda
      postulate
        isSlotLeader : IsSlotLeader p₁ (MkSlotNumber 1) prf
        isBlockSignature : IsBlockSignature b sig

        isCommitteeMember : IsCommitteeMember p₁ (MkRoundNumber 1) prf'
        isVoteSignature : IsVoteSignature v sig'
```
Properties of cert₀
```agda
      cert₀PointsIntoValidChain : ∀ {c} → ValidChain {block₀} {IsSlotLeader} {IsBlockSignature} c → cert₀ PointsInto c
      cert₀PointsIntoValidChain {.(block₀ ∷ [])} Genesis = here refl
      cert₀PointsIntoValidChain {.(_ ∷ _ ∷ _)} (Cons _ _ _ v) = there (cert₀PointsIntoValidChain v)
```
Based on properties of the blocktree we can show the following
```agda
      open IsTreeType

      latestCert-extendTree≡latestCert : ∀ {t b} → latestCertSeen (extendTree t b) ≡ latestCertSeen t
      latestCert-extendTree≡latestCert {t} {b} = cong (latestCert cert₀) $ extendable-certs is-TreeType t b

      latestCert≡cert₀' : latestCertSeen tree₀ ≡ cert₀
      latestCert≡cert₀' rewrite instantiated-certs is-TreeType = refl
```
Execution trace of the protocol
```agda
      _ : initialState ↝⋆ finalState
      _ =    NextSlot empty  -- slot 1
          ↣ CreateBlock (honest refl refl isBlockSignature isSlotLeader)
          ↣ Deliver (honest refl (here refl) BlockReceived)
          ↣ NextSlot empty  -- slot 2
          ↣ CastVote (honest refl refl isVoteSignature refl isCommitteeMember (Regular vr-1a vr-1b))
          ↣ Deliver (honest refl (here refl) VoteReceived)
          ↣ NextSlot empty  -- slot 3
          ↣ ∎
```
Trace dependent properties
```agda
          where
            latestCert≡cert₀ : latestCertSeen (extendTree tree₀ b) ≡ cert₀
            latestCert≡cert₀ = trans latestCert-extendTree≡latestCert latestCert≡cert₀'

            vr-1a : 1 ≡ roundNumber (latestCertSeen (extendTree tree₀ b)) + 1
            vr-1a rewrite latestCert≡cert₀ = refl

            vr-1b : (latestCertSeen (extendTree tree₀ b))
              PointsInto (bestChain (MkSlotNumber 2) (extendTree tree₀ b))
            vr-1b rewrite latestCert≡cert₀ = cert₀PointsIntoValidChain $
              valid is-TreeType (extendTree tree₀ b) (MkSlotNumber 2)
```
