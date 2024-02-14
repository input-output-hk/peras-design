module Peras.SmallStep where

open import Data.Bool using (Bool; true; false)
open import Data.List as List using (List; all; foldr; _∷_; []; _++_; filter; filterᵇ; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe
open import Data.Nat using (suc; pred; _≤_; _≤ᵇ_)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
open import Data.Tree.AVL.Sets renaming (⟨Set⟩ to set) using ()

open import Function.Base using (_∘_; id)
open import Level using (0ℓ)
open import Relation.Binary using (DecidableEquality; StrictTotalOrder)
open import Relation.Nullary using (Dec; yes; no)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; subst; trans)

open import Function.Base using (id)

open import Peras.Chain using (Chain⋆; isValidChain)
open import Peras.Crypto using (Hash; HashO; hash; emptyBS)
open import Peras.Block using (PartyId; PartyIdO; Block⋆; BlockO; Slot; slotNumber; Tx; Honesty)

open import Data.Tree.AVL.Sets as S using ()
open import Data.Tree.AVL.Sets BlockO as B renaming (⟨Set⟩ to set) using (singleton; size; insert; toList)
open import Data.Tree.AVL.Map PartyIdO as M using (Map; lookup; insert; empty)
open import Data.List.Relation.Binary.Subset.Propositional {A = Block⋆} using (_⊆_)

{-
  Formalizing Nakamoto-Style Proof of Stake
  Søren Eller Thomsen and Bas Spitters
-}

Blocks⋆ = B.⟨Set⟩

open Chain⋆ public
open Honesty public

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

  module _ {T : Set} (honest? : (p : PartyId) → Honesty p) where

    -- local state

    Stateˡ = LocalState {T}

    data Progress : Set where
      Ready : Progress
      Delivered : Progress
      Baked : Progress

    data Message : Set where
      BlockMsg : Block⋆ → Message

    postulate
      _≟-Message_ : DecidableEquality Message

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
        execution-order : List PartyId -- TODO: List (Honesty p)

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

    data _[_]⇀_ : {p : PartyId} → Stateᵍ → Honesty p → Stateᵍ → Set where

      honestNoState : ∀ {p N}
        → lookup (stateMap N) p ≡ nothing
          -------------------------------
        → N [ Honest {p} ]⇀ N

      honest : ∀ {p N} {sₗ sₗ′ : Stateˡ} {msgs}
        → lookup (stateMap N) p ≡ just sₗ
        → msgs ≡ proj₁ (fetchMsgs p N)
        → sₗ′ ≡ honestRcv msgs (clock N) sₗ
          --------------------------------
        → N [ Honest {p} ]⇀
          record N {
              stateMap = M.insert p sₗ′ (stateMap N)
            }

      corrupt : ∀ {p N}
          ---------------------
        → N [ Corrupt {p} ]⇀ N

    []⇀-does-not-modify-messages : ∀ {M N p} {h : Honesty p}
      → M [ h ]⇀ N
      → messages M ≡ messages N
    []⇀-does-not-modify-messages (honestNoState _) = refl
    []⇀-does-not-modify-messages (honest _ _ _) = refl -- why?
    []⇀-does-not-modify-messages corrupt = refl

    data _⇀_ : Stateᵍ → Stateᵍ → Set where

      Empty : ∀ {M}
        → execution-order M ≡ []
          ----------------------
        → M ⇀ M

      Cons : ∀ {M p ps} {N} {O}
        → execution-order M ≡ p ∷ ps
        → (record M { execution-order = ps }) [ honest? p ]⇀ N
        → N ⇀ O
          ------
        → M ⇀ O

    ⇀-does-not-modify-messages : ∀ {M N}
      → M ⇀ N
      → messages M ≡ messages N
    ⇀-does-not-modify-messages (Empty _) = refl
    ⇀-does-not-modify-messages (Cons _ x₁ x₂) =
      trans
        ([]⇀-does-not-modify-messages x₁)
        (⇀-does-not-modify-messages x₂)

    -- create

    data _[_]↷_ : {p : PartyId} → Stateᵍ → Honesty p → Stateᵍ → Set where

      honestNoState : ∀ {p N}
        → lookup (stateMap N) p ≡ nothing
          -------------------------------
        → N [ Honest {p} ]↷ N

      honest : ∀ {p N} {sₗ sₗ′ : Stateˡ} {msgs}
        → (msgs , sₗ′) ≡ honestCreate (clock N) [] sₗ
          --------------------------------
        → N [ Honest {p} ]↷
          record N {
              stateMap = M.insert p sₗ′ (stateMap N);
              messages = msgs ++ messages N
            }

      corrupt : ∀ {p N}
          ---------------------
        → N [ Corrupt {p} ]↷ N

    open import Data.List.Relation.Binary.Subset.Propositional {A = Message} renaming (_⊆_ to _⊆ᴹ_) using ()
    open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-trans)
    open import Data.List.Membership.DecPropositional _≟-Message_ using (_∈?_)

    data _↷_ : Stateᵍ → Stateᵍ → Set where

      Empty : ∀ {M}
        → execution-order M ≡ []
          ----------------------
        → M ↷ M

      Cons : ∀ {M p ps} {N} {O}
        → execution-order M ≡ p ∷ ps
        → (record M { execution-order = ps }) [ honest? p ]↷ N
        → N ↷ O
          ------
        → M ↷ O

    -- small-step semantics for global state evolution

    data _↝_ : Stateᵍ → Stateᵍ → Set where

      Deliver : ∀ {s sm ms ps} {N}
        → let M = ⟪ s , Ready , sm , ms , ps ⟫
           in M ⇀ N
              ---------------------------
            → M ↝ record N {
                     progress = Delivered
                   }

      Bake : ∀ {s sm ms ps} {N}
        → let M = ⟪ s , Delivered , sm , ms , ps ⟫
           in M ↷ N
              -----------------------
            → M ↝ record N {
                     progress = Baked
                   }

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

    -- hash function, collision free predicate

    module _ {hashᴮ : Block⋆ → Hash} where

      data CollisionFree (N : Stateᵍ) : Set where

        collision-free : ∀ {b₁ b₂ : Block⋆}
          → BlockMsg b₁ ∈ messages N
          → BlockMsg b₂ ∈ messages N
          → hashᴮ b₁ ≡ hashᴮ b₂
          → b₁ ≡ b₂
          → CollisionFree N

      subst′ : ∀ {A : Set} {x : A} {xs ys : List A}
        → x ∈ xs
        → xs ≡ ys
        → x ∈ ys
      subst′ {A} {x} x₁ x₂ = subst (x ∈_) x₂ x₁

      -- When the current state is collision free, the pervious state was so too

      postulate
        []↷-collision-free : ∀ {M N p} {h : Honesty p}
          → CollisionFree N
          → M [ h ]↷ N
          → CollisionFree M

        ↷-collision-free : ∀ {M N}
          → CollisionFree N
          → M ↷ N
          → CollisionFree M

        ↝-collision-free : ∀ {N₁ N₂ : Stateᵍ}
          → N₁ ↝ N₂
          → CollisionFree N₂
            ----------------
          → CollisionFree N₁

      {-
      ↝-collision-free (Deliver (Empty refl)) (collision-free x x₁ x₂ x₃) = collision-free x x₁ x₂ x₃
      ↝-collision-free (Deliver (Cons refl x₅ y)) (collision-free x x₁ x₂ x₃) =
        let xx = trans ([]⇀-does-not-modify-messages x₅) (⇀-does-not-modify-messages2 y)
        in collision-free (subst′ x (sym xx)) (subst′ x₁ (sym xx)) x₂ x₃
      ↝-collision-free (Bake (Empty refl)) (collision-free x x₁ x₂ x₃) = collision-free x x₁ x₂ x₃
      ↝-collision-free (Bake (Cons refl x₅ y)) a =
        let aa = ↷-collision-free2 {!!} y
            bb = ↷-collision-free aa x₅
        in {!!} -- collision-free {!!} {!!} x₂ x₃

      ↝-collision-free NextRound (collision-free x x₁ x₂ x₃) = collision-free x x₁ x₂ x₃
      ↝-collision-free PermParties (collision-free x x₁ x₂ x₃) = collision-free x x₁ x₂ x₃
      ↝-collision-free PermMsgs (collision-free x x₁ x₂ x₃) = collision-free x x₁ x₂ x₃
      -}

      -- When the current state is collision free, pervious states were so too

      ↝⋆-collision-free : ∀ {N₁ N₂ : Stateᵍ}
        → N₁ ↝⋆ N₂
        → CollisionFree N₂
          ----------------
        → CollisionFree N₁
      ↝⋆-collision-free (_ ∎) N = N
      ↝⋆-collision-free (_ ↝⟨ N₁↝N₂ ⟩ N₂↝⋆N₃) N₃ =
        ↝-collision-free N₁↝N₂ (↝⋆-collision-free N₂↝⋆N₃ N₃)
