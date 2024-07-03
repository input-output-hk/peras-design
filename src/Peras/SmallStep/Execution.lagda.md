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
open import Data.Nat using (_+_; _*_; _≟_)
open import Data.Nat.Properties using (+-identityˡ; +-identityʳ)
open import Function using (_∘_; id; _$_; flip)

open import Peras.Chain
open import Peras.Crypto hiding (isCommitteeMember)
open import Peras.Block
open import Peras.Numbering
open import Peras.Params
open import Peras.SmallStep

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym; subst; trans)

open import Prelude.AssocList
open import Prelude.DecEq using (DecEq)
open import Prelude.Default using (Default)
open Default ⦃...⦄
```
-->
```agda
module _ ⦃ _ : Postulates ⦄
         ⦃ _ : Hashable Block ⦄
         ⦃ _ : Hashable (List Tx) ⦄
         ⦃ _ : Network ⦄
         where

  open Postulates ⦃...⦄
  open Network ⦃...⦄
  open Hashable ⦃...⦄

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

      GlobalState = State {T} {blockTree} {S} {adversarialState₀} {txSelection} {parties}
```
```agda
      createBlock' : SlotNumber → PartyId → T → Block
      createBlock' s p t =
        let
          π = createLeadershipProof s p
          σ = createBlockSignature p
        in createBlock {T} {blockTree} {S} {adversarialState₀} {txSelection} {parties} s p π σ t
```
```agda
      createVote' : SlotNumber → PartyId → T → Vote
      createVote' s p t =
        let
          r = v-round s
          π = createMembershipProof r p
          σ = createVoteSignature p
        in createVote {T} {blockTree} {S} {adversarialState₀} {txSelection} {parties} s p π σ t
```
Blocks and Votes
```agda
      block₁ : Block
      block₁ = createBlock' (MkSlotNumber 1) party₁ tree₀

      chain₁ : Chain
      chain₁ = block₁ ∷ preferredChain tree₀

      vote₁ : Vote
      vote₁ = createVote' (MkSlotNumber 2) party₁ (newChain tree₀ chain₁)

      block₃ : Block
      block₃ = createBlock' (MkSlotNumber 3) party₂ (addVote (newChain tree₀ chain₁) vote₁)
```
Initial state
```agda
      initialState : GlobalState
      initialState = ⟦ MkSlotNumber 0 , initialMap , [] , [] , adversarialState₀ ⟧
        where
          initialMap = (party₁ , tree₀) ∷ (party₂ , tree₀) ∷ []
```
Final state after the execution of all the steps
```agda
      finalState : GlobalState
      finalState = ⟦ MkSlotNumber 3 , finalMap , [] , finalMsg , adversarialState₀ ⟧
        where
          -- finalMsg = BlockMsg block₃ ∷ VoteMsg vote₁ ∷ BlockMsg block₁ ∷ []
          -- finalTree = extendTree (addVote (extendTree tree₀ block₁) vote₁) block₃
          finalMsg = VoteMsg vote₁ ∷ ChainMsg chain₁ ∷ []
          finalTree = addVote (newChain tree₀ chain₁) vote₁
          finalMap = (party₁ , finalTree) ∷ (party₂ , finalTree) ∷ []
```
Properties of cert₀
```agda
      cert₀PointsIntoValidChain : ∀ {c} → ValidChain c → cert₀ PointsInto c
      cert₀PointsIntoValidChain {.(block₀ ∷ [])} Genesis = here refl
      cert₀PointsIntoValidChain {.(_ ∷ _)} (Cons _ _ _ _ v) = there (cert₀PointsIntoValidChain v)
```
Based on properties of the blocktree we can show the following
```agda
      open IsTreeType
      open import Data.Bool using (true; false; _∧_; not)
      open import Data.Nat using (_<ᵇ_)
      open import Data.List using (_++_; catMaybes; any)
      open import Haskell.Prim.List using (map)
      open import Relation.Nullary.Decidable hiding (map)

      latestCertSeen-tree₀≡cert₀ : latestCertSeen tree₀ ≡ cert₀
      latestCertSeen-tree₀≡cert₀ rewrite is-TreeType .instantiated-certs = refl

      latestCertOnChain-tree₀≡cert₀ : latestCertOnChain tree₀ ≡ cert₀
      latestCertOnChain-tree₀≡cert₀
        rewrite is-TreeType .instantiated
        rewrite is-TreeType .genesis-block-no-certificate = refl

      roundNumber-latestCertSeen-tree₀≡0 : roundNumber (latestCertSeen tree₀) ≡ 0
      roundNumber-latestCertSeen-tree₀≡0 rewrite latestCertSeen-tree₀≡cert₀ = refl

      x∧false≡false : ∀ {x} → x ∧ false ≡ false
      x∧false≡false {false} = refl
      x∧false≡false {true} = refl

      needCert-tree₀≡nothing : needCert {T} {blockTree} {S} {adversarialState₀} {txSelection} {parties}
                (MkRoundNumber 0) tree₀ ≡ nothing
      needCert-tree₀≡nothing
        rewrite roundNumber-latestCertSeen-tree₀≡0
        rewrite x∧false≡false {not (any (λ {c → ⌊ roundNumber c + 2 ≟ 0 ⌋}) (certs tree₀))}
        = refl

      catMaybes≡[] : catMaybes (map certificate (preferredChain tree₀)) ≡ []
      catMaybes≡[]
        rewrite is-TreeType .instantiated
        rewrite is-TreeType .genesis-block-no-certificate = refl

      noNewCert : certs (newChain tree₀ chain₁) ≡ cert₀ ∷ []
      noNewCert =
        let
          s₁ = is-TreeType .extendable-chain tree₀ chain₁
          s₂ = is-TreeType .instantiated-certs
          s₃ = trans s₁ (cong (_++ certs tree₀) r₂)
        in trans s₃ s₂
        where
          r₁ : catMaybes (map certificate chain₁) ≡ []
          r₁ rewrite needCert-tree₀≡nothing rewrite catMaybes≡[] = refl

          r₂ : certsFromChain chain₁ ≡ []
          r₂ rewrite r₁ = refl

      latestCert-newChain≡latestCert : latestCertSeen (newChain tree₀ chain₁) ≡ latestCertSeen tree₀
      latestCert-newChain≡latestCert = trans r (sym latestCertSeen-tree₀≡cert₀)
        where
          r : latestCertSeen (newChain tree₀ chain₁) ≡ cert₀
          r rewrite noNewCert = refl

      latestCert≡cert₀ : latestCertSeen (newChain tree₀ chain₁) ≡ cert₀
      latestCert≡cert₀ = trans latestCert-newChain≡latestCert latestCertSeen-tree₀≡cert₀
```
Execution trace of the protocol
```agda
      module _
        (isSlotLeader : ∀ {p} {s} → IsSlotLeader p s (createLeadershipProof s p))
        (isBlockSignature : ∀ {b} → IsBlockSignature b (createBlockSignature (creatorId b)))
        (isCommitteeMember : ∀ {p} {s} → IsCommitteeMember p s (createMembershipProof s p))
        (isVoteSignature : ∀ {v} → IsVoteSignature v (createVoteSignature (creatorId v)))

        where
        validChain₁ : ValidChain chain₁
        validChain₁ =
          let v = is-TreeType .valid tree₀
              ((_ , d), pr) = uncons v
          in Cons {c₁ = d} isBlockSignature isSlotLeader refl pr v

{-
        _ : initialState ↝⋆ finalState
        _ = NextSlot empty refl                           -- slot 1
          ↣ CreateBlock empty (honest refl validChain₁)
          ↣ Fetch (honest refl (here refl) ChainReceived)
          ↣ NextSlotNewRound empty refl {!!}              -- slot 2
          ↣ CreateVote empty (honest refl isVoteSignature refl isCommitteeMember (Regular vr-1a vr-1b))
          ↣ Fetch (honest refl (here refl) VoteReceived)
          ↣ NextSlot empty refl                           -- slot 3
--          ↣ CreateBlock (honest refl refl isBlockSignature isSlotLeader)
--          ↣ Deliver (honest refl (here refl) ChainReceived)
--          ↣ NextSlotNewRound empty refl ?  -- slot 4
--          ↣ NextSlot empty refl -- slot 5
--          ↣ NextSlotNewRound empty refl ? -- slot 6
          ↣ ∎
-}
```
Trace dependent properties
```agda
{-
          where
            vr-1a : 1 ≡ roundNumber (latestCertSeen (newChain tree₀ chain₁)) + 1
            vr-1a rewrite latestCert≡cert₀ = refl

            vr-1b : (latestCertSeen (newChain tree₀ chain₁))
              PointsInto (preferredChain (newChain tree₀ chain₁))
            vr-1b rewrite latestCert≡cert₀ = cert₀PointsIntoValidChain $
              valid is-TreeType (newChain tree₀ chain₁)
-}
```
