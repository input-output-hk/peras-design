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
open import Data.Tree.AVL.Map.Relation.Unary.Any PartyIdO as Mapₚ using ()
open import Data.Tree.AVL.Relation.Unary.Any PartyIdO as B using ()
open import Data.Tree.AVL.Indexed.Relation.Unary.Any PartyIdO as C using ()

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym; subst; trans)
```
-->
```agda
module _ {block₀}
         ⦃ _ : Postulates ⦄
         ⦃ _ : Hashable Block ⦄
         ⦃ _ : Hashable (List Tx) ⦄
         where

  open Postulates ⦃...⦄
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
           (createLeadershipProof : SlotNumber → PartyId → LeadershipProof)
           (createMembershipProof : RoundNumber → PartyId → MembershipProof)
           (createBlockSignature : PartyId → Signature)
           (createVoteSignature : PartyId → Signature)
           where

    open TreeType blockTree

    private
```
This is a very simple example of the execution of the protocol in the small-step semantics. There are only 2 parties and both parties are honest. The first party is the slot leader in the first slot and creates a block. The block is then delivered to the second party. The second party receives the block and the protocol moves to the next slot.
```agda
      party₁ party₂ : PartyId
      party₁ = 1
      party₂ = 2

      parties : Parties
      parties = (party₁ , Honest) ∷ (party₂ , Honest) ∷ []

      GlobalState = State {block₀} {cert₀} {T} {blockTree} {S} {adversarialState₀} {txSelection} {parties}
```
```agda
      createBlock : PartyId → SlotNumber → Block → Block
      createBlock p s b = record
            { slotNumber = s
            ; creatorId = p
            ; parentBlock = hash b
            ; certificate = nothing
            ; leadershipProof = createLeadershipProof s p
            ; bodyHash = bodyHash′
            ; signature = createBlockSignature p
            }
        where
          txs = txSelection s p
          bodyHash′ = blockHash record
                       { blockHash = hash txs
                       ; payload = txs
                       }
```
```agda
      createVote : PartyId → RoundNumber → Block → Vote
      createVote p r b = record
            { votingRound = r
            ; creatorId = p
            ; proofM = createMembershipProof r p
            ; blockHash = hash b
            ; signature = createVoteSignature p
            }
```
Blocks and Votes
```agda
      block₁ : Block
      block₁ = createBlock party₁ (MkSlotNumber 1) (tipBest (MkSlotNumber 1) tree₀) -- TODO: block₀

      vote₁ : Vote
      vote₁ = createVote party₁ (MkRoundNumber 1) (tipBest (MkSlotNumber 1) (extendTree tree₀ block₁)) -- TODO: block₁

      block₃ : Block
      block₃ = createBlock party₂ (MkSlotNumber 3) (tipBest (MkSlotNumber 3) (addVote (extendTree tree₀ block₁) vote₁)) -- TODO: block₁
```
Initial state
```agda
      initialState : GlobalState
      initialState = ⟦ MkSlotNumber 0 , initialMap , [] , [] , adversarialState₀ ⟧
        where
          initialMap = fromList ((party₁ , tree₀) ∷ (party₂ , tree₀) ∷ [])
```
Final state after the execution of all the steps
```agda
      finalState : GlobalState
      finalState = ⟦ MkSlotNumber 3 , finalMap , [] , finalMsg , adversarialState₀ ⟧
        where
          -- finalMsg = BlockMsg block₃ ∷ VoteMsg vote₁ ∷ BlockMsg block₁ ∷ []
          -- finalTree = extendTree (addVote (extendTree tree₀ block₁) vote₁) block₃
          finalMsg = VoteMsg vote₁ ∷ BlockMsg block₁ ∷ []
          finalTree = addVote (extendTree tree₀ block₁) vote₁
          finalMap = fromList ((party₁ , finalTree) ∷ (party₂ , finalTree) ∷ [])
```
Properties of cert₀
```agda
      cert₀PointsIntoValidChain : ∀ {c} → ValidChain {block₀} c → cert₀ PointsInto c
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
      module _
        (isSlotLeader : ∀ {p} {s} → IsSlotLeader p s (createLeadershipProof s p))
        (isBlockSignature : ∀ {b} → IsBlockSignature b (createBlockSignature (creatorId b)))
        (isCommitteeMember : ∀ {p} {s} → IsCommitteeMember p s (createMembershipProof s p))
        (isVoteSignature : ∀ {v} → IsVoteSignature v (createVoteSignature (creatorId v)))

        where
        _ : initialState ↝⋆ finalState
        _ =  NextSlot empty refl -- slot 1
          ↣ CreateBlock (honest refl refl isBlockSignature isSlotLeader)
          ↣ Deliver (honest refl (here refl) BlockReceived)
          ↣ NextSlotNewRound empty refl (B.tree (C.here {!!})) -- slot 2
          ↣ CastVote (honest refl refl isVoteSignature refl isCommitteeMember (Regular vr-1a vr-1b))
          ↣ Deliver (honest refl (here refl) VoteReceived)
          ↣ NextSlot empty refl -- slot 3
--          ↣ CreateBlock (honest refl refl isBlockSignature isSlotLeader)
--          ↣ Deliver (honest refl (here refl) BlockReceived)
--
-- Checking Peras.SmallStep.Execution (/build/zz1xvsqhxyydv60s1wr35yx8wpib5h1x-source/src/Peras/SmallStep/Execution.lagda.md).
-- agda: Heap exhausted;
-- agda: Current maximum heap size is 3758096384 bytes (3584 MB).
-- agda: Use `+RTS -M<size>' to increase it.
--
--          ↣ NextSlotNewRound empty refl ?  -- slot 4
--          ↣ NextSlot empty refl -- slot 5
--          ↣ NextSlotNewRound empty refl ? -- slot 6
          ↣ ∎
```
Trace dependent properties
```agda
          where
            latestCert≡cert₀ : latestCertSeen (extendTree tree₀ block₁) ≡ cert₀
            latestCert≡cert₀ = trans latestCert-extendTree≡latestCert latestCert≡cert₀'

            vr-1a : 1 ≡ roundNumber (latestCertSeen (extendTree tree₀ block₁)) + 1
            vr-1a rewrite latestCert≡cert₀ = refl

            vr-1b : (latestCertSeen (extendTree tree₀ block₁))
              PointsInto (bestChain (MkSlotNumber 2) (extendTree tree₀ block₁))
            vr-1b rewrite latestCert≡cert₀ = cert₀PointsIntoValidChain $
              valid is-TreeType (extendTree tree₀ block₁) (MkSlotNumber 2)
```
