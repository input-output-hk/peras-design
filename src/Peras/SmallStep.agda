module Peras.SmallStep where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; all; foldr; _∷_; []; _++_; filter; filterᵇ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe
open import Data.Nat using (suc; pred; _≤_; _≤ᵇ_)
open import Data.Product using (_,_; _×_)
open import Data.Tree.AVL.Sets renaming (⟨Set⟩ to set) using ()

open import Function.Base using (_∘_; id)
open import Level using (0ℓ)
open import Relation.Binary using (StrictTotalOrder)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; subst)

open import Function.Base using (id)

open import Peras.Chain using (Chain⋆; isValidChain)
open import Peras.Crypto using (Hash; HashO; hash; emptyBS)
open import Peras.Block using (PartyId; PartyIdO; Block⋆; BlockO; Slot; slotNumber; Tx)

open import Data.Tree.AVL.Sets as S using ()
open import Data.Tree.AVL.Sets BlockO as B renaming (⟨Set⟩ to set) using (singleton; size; insert; toList)
open import Data.Tree.AVL.Map PartyIdO as M using (Map; lookup; insert; empty)
open import Data.List.Relation.Binary.Subset.Propositional {A = Block⋆} using (_⊆_)

{-
  Formalizing Nakamoto-Style Proof of Stake
  Søren Eller Thomsen and Bas Spitters
-}

data Honesty : Set where
  Honest : Honesty
  Corrupt : Honesty

Blocks⋆ = B.⟨Set⟩

open Chain⋆ public

-- parameterized with genesis block

module _ {block₀ : Block⋆} where

  -- TODO: Peras
  record IsTreeType {T : Set}
                    (tree₀ : T)
                    (extendTree : T → Block⋆ → T)
                    (allBlocks : T → Blocks⋆)
                    (bestChain : Slot → T → Chain⋆)
         : Set where

    field

      instantiated :
        allBlocks tree₀ ≡ singleton block₀

      extendable : ∀ (t : T) (b : Block⋆)
        → allBlocks (extendTree t b) ≡ B.insert b (allBlocks t)

      valid : ∀ (t : T) (sl : Slot)
        → isValidChain (bestChain sl t) ≡ true

      optimal : ∀ (c : Chain⋆) (t : T) (sl : Slot)
        → isValidChain c ≡ true
        → toList (blocks c) ⊆ filterᵇ (λ {b → slotNumber b ≤ᵇ sl}) (toList (allBlocks t))
        → size (blocks c) ≤ size (blocks (bestChain sl t))

      self-contained : ∀ (t : T) (sl : Slot)
        → toList (blocks (bestChain sl t)) ⊆ filterᵇ (λ {b → slotNumber b ≤ᵇ sl}) (toList (allBlocks t))

  record TreeType (T : Set) : Set where

    field
      tree₀ : T
      extendTree : T → Block⋆ → T
      allBlocks : T → Blocks⋆
      bestChain : Slot → T → Chain⋆

      is-TreeType : IsTreeType tree₀ extendTree allBlocks bestChain

  open TreeType

  record LocalState {T : Set} : Set where

    constructor ⟨_,_,_⟩

    field
      partyId : PartyId
      tT : TreeType T
      tree : T

  module _ {T : Set} (honest? : PartyId → Honesty) where

    -- local state

    Stateˡ = LocalState {T}

    data Progress : Set where
      Ready : Progress
      Delivered : Progress
      Baked : Progress

    data Message : Set where
      BlockMsg : Block⋆ → Message

    extendTreeₗ : Stateˡ → Block⋆ → Stateˡ
    extendTreeₗ ⟨ partyId , tT , tree ⟩ b = ⟨ partyId , tT , (extendTree tT) tree b ⟩

    processMsg : Message → Stateˡ → Stateˡ
    processMsg (BlockMsg b) sₗ = extendTreeₗ sₗ b

    honestRcv : List Message → Slot → Stateˡ → Stateˡ
    honestRcv msgs _ sₗ = foldr processMsg sₗ msgs

    lottery : PartyId → Slot → Bool
    lottery _ _ = false -- FIXME

    honestCreate : Slot → List Tx → Stateˡ → List Message × Stateˡ
    honestCreate sl txs ⟨ p , tT , tree ⟩ with lottery p sl
    ... | true = let best = (bestChain tT) (pred sl) tree
                     parent = record { hash = emptyBS } -- FIXME
                     newBlock = record {
                         slotNumber = sl ;
                         creatorId = p ;
                         parentBlock = parent ;
                         includedVotes = S.empty HashO ; -- TODO: Peras
                         leadershipProof = record { proof = emptyBS } ; -- FIXME
                         payload = txs ;
                         signature = record { signature = emptyBS } -- FIXME
                       }
                  in BlockMsg newBlock ∷ [] , ⟨ p , tT , (extendTree tT) tree newBlock ⟩
    ... | false = [] , ⟨ p , tT , tree ⟩

    -- global state

    record Stateᵍ : Set where
      constructor ⟪_,_,_,_,_⟫
      field
        clock : Slot
        progress : Progress
        stateMap : Map Stateˡ
        messages : List Message
        execution-order : List PartyId

    open Stateᵍ public

    -- initial global state

    N₀ : Stateᵍ
    N₀ = ⟪ 0 , Ready , empty , [] , [] ⟫ -- FIXME: initial parties as parameter

    permParties : List PartyId → List PartyId
    permParties = id -- FIXME: permute

    permMessages : List Message → List Message
    permMessages = id -- FIXME: permute

    updateStateˡ : PartyId → Stateˡ → Stateᵍ → Stateᵍ
    updateStateˡ p sₗ N = record N { stateMap = M.insert p sₗ (stateMap N) }

    -- network

    fetchMsgs : PartyId → Stateᵍ → List Message × Stateᵍ
    fetchMsgs _ N = (messages N , N) -- FIXME: * implement network model with delays
                                     --        * filter messages

    -- receive

    party↓ : PartyId → Stateᵍ → Stateᵍ
    party↓ p N with lookup (stateMap N) p | honest? p
    ... | just sₗ | Honest = let msgs , N′ = fetchMsgs p N
                                 sₗ′       = honestRcv msgs (clock N) sₗ
                              in updateStateˡ p sₗ′ N′
    ... | just sₗ | Corrupt = N -- FIXME: implement adversary
    ... | nothing | _ = N

    -- create

    party↷ : PartyId → Stateᵍ → Stateᵍ
    party↷ p N with lookup (stateMap N) p | honest? p
    ... | just sₗ | Honest = let msgs , sₗ′ = honestCreate (clock N) [] sₗ
                             -- FIXME: gossip msgs
                              in updateStateˡ p sₗ′ N
    ... | just sₗ | Corrupt = N -- FIXME: implement adversary
    ... | nothing | _ = N


    -- small-step semantics for global state evolution

    data _↝_ : Stateᵍ → Stateᵍ → Set where

      Deliver : ∀ {s sm ms ps}
        → let
            M = ⟪ s , Ready , sm , ms , ps ⟫
            N = record (foldr party↓ M ps) { progress = Delivered }
          in
            M ↝ N

      Bake : ∀ {s sm ms ps}
        → let
            M = ⟪ s , Delivered , sm , ms , ps ⟫
            N = record (foldr party↷ M ps) { progress = Baked }
          in
            M ↝ N

      NextRound : ∀ {s sm ms ps}
        → ⟪ s , Baked , sm , ms , ps ⟫ ↝ ⟪ suc s , Ready , sm , ms , ps ⟫

      PermParties : ∀ {s p sm ms ps}
        → ⟪ s , p , sm , ms , ps ⟫ ↝ ⟪ s , p , sm , ms , permParties ps ⟫

      PermMsgs : ∀ {s p sm ms ps}
        → ⟪ s , p , sm , ms , ps ⟫ ↝ ⟪ s , p , sm , permMessages ms , ps ⟫


    -- reflexive, transitive closure (which is big-step in the paper)

    infix  2 _↝⋆_
    infixr 2 _↝⟨_⟩_
    infix  3 _∎

    data _↝⋆_ : Stateᵍ → Stateᵍ → Set where

      _∎ : ∀ M
          -------
        → M ↝⋆ M

      _↝⟨_⟩_ : ∀ L {M N}
        → L ↝ M
        → M ↝⋆ N
          ------
        → L ↝⋆ N


    module _ {hashᴮ : Block⋆ → Hash} where

      data CollisionFree (N : Stateᵍ) : Set where

        collision-free : ∀ {b₁ b₂ : Block⋆}
          → BlockMsg b₁ ∈ messages N
          → BlockMsg b₂ ∈ messages N
          → hashᴮ b₁ ≡ hashᴮ b₂
          → b₁ ≡ b₂
          → CollisionFree N

      {-
      party↓-does-not-change-msg : ∀ {p N₁ N₂}
        → party↓ p N₁ ≡ N₂
        → messages N₁ ≡ messages N₂
      party↓-does-not-change-msg = {!!}

      foldr-party↓-does-not-change-msg : ∀ {N ps}
        → messages (foldr party↓ N ps) ≡ messages N
      foldr-party↓-does-not-change-msg {N} {[]} = refl
      foldr-party↓-does-not-change-msg {N} {x ∷ ps} =
        let xx = foldr-party↓-does-not-change-msg {N} {ps}
            yy = party↓-does-not-change-msg {x} {foldr party↓ N ps} {N}
        in {!!}

      subst′ : ∀ {A : Set} {x : A} {xs ys : List A}
        → x ∈ xs
        → xs ≡ ys
        → x ∈ ys
      subst′ {A} {x} x₁ x₂ = subst (x ∈_) x₂ x₁
      -}

      postulate
        ↝-collision-free : ∀ {N₁ N₂ : Stateᵍ}
          → N₁ ↝ N₂
          → CollisionFree N₂
          → CollisionFree N₁

      {-
      ↝-collision-free {⟪ s , Ready , sm , ms , ps ⟫} Deliver (collision-free b₁∈m b₂∈m x₂ x₃) =
        let msg-≡ = foldr-party↓-does-not-change-msg {⟪ s , Ready , sm , ms , ps ⟫} {ps}
        in collision-free (subst′ b₁∈m msg-≡) (subst′ b₂∈m msg-≡) x₂ x₃
      ↝-collision-free Bake (collision-free x x₁ x₂ x₃) = collision-free {!!} {!!} x₂ x₃
      ↝-collision-free NextRound (collision-free x x₁ x₂ x₃) = collision-free x x₁ x₂ x₃
      ↝-collision-free PermParties (collision-free x x₁ x₂ x₃) = collision-free x x₁ x₂ x₃
      ↝-collision-free PermMsgs (collision-free x x₁ x₂ x₃) = collision-free x x₁ x₂ x₃
      -}

      ↝⋆-collision-free : ∀ {N₁ N₂ : Stateᵍ}
        → N₁ ↝⋆ N₂
        → CollisionFree N₂
        → CollisionFree N₁
      ↝⋆-collision-free (_ ∎) N = N
      ↝⋆-collision-free (_ ↝⟨ N₁↝N₂ ⟩ N₂↝⋆N₃) N₃ = ↝-collision-free N₁↝N₂ (↝⋆-collision-free N₂↝⋆N₃ N₃)
