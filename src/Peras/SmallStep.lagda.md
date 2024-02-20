---
title: Marlowe.Language
layout: page
---

```agda
module Peras.SmallStep where
```

<!--
```agda
open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.Fin using (Fin; fromℕ; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.List as List using (List; all; foldr; _∷_; []; _++_; filter; filterᵇ; map; cartesianProduct)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
open import Data.Maybe using (just; nothing)
open import Data.Nat using (suc; pred; _≤_; _≤ᵇ_)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
open import Function.Base using (_∘_; id)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; subst; trans)

open import Peras.Chain using (Chain⋆; ValidChain)
open import Peras.Crypto using (Hash; HashO; hash; emptyBS)
open import Peras.Block using (PartyId; PartyIdO; _≟-PartyId_; Block⋆; BlockO; Blocks⋆; Slot; slotNumber; Tx; Honesty)

open import Data.Tree.AVL.Sets as S using ()
open import Data.Tree.AVL.Sets BlockO as B renaming (⟨Set⟩ to set) using (singleton; size; insert; toList)
open import Data.Tree.AVL.Map PartyIdO as M using (Map; lookup; insert; empty)
open import Data.List.Relation.Binary.Subset.Propositional {A = Block⋆} using (_⊆_)

open Chain⋆ public
open Honesty public
```
-->

# Small-step semantics

Reference: Formalizing Nakamoto-Style Proof of Stake by Søren Eller Thomsen and Bas Spitters

```agda
data Progress : Set where
   Ready : Progress
   Delivered : Progress
   Baked : Progress

-- TODO: use Peras.Message
data Message : Set where
   BlockMsg : Block⋆ → Message


record MessageTup : Set where
  constructor ⦅_,_,_⦆
  field
    msg : Message
    rcv : PartyId
    cd : Fin 3
```

## Parameterized with genesis block

```agda
module _ {block₀ : Block⋆} where


  ```
  ## BlockTree

  ```agda
  record IsTreeType {T : Set}
                    (tree₀ : T)
                    (extendTree : T → Block⋆ → T)
                    (allBlocks : T → Blocks⋆)
                    (bestChain : Slot → T → Chain⋆)
         : Set₁ where

    field

      instantiated :
        allBlocks tree₀ ≡ singleton block₀

      extendable : ∀ (t : T) (b : Block⋆)
        → allBlocks (extendTree t b) ≡ B.insert b (allBlocks t)

      valid : ∀ (t : T) (sl : Slot)
        → ValidChain (bestChain sl t)

      -- TODO: drop `toList`?
      optimal : ∀ (c : Chain⋆) (t : T) (sl : Slot)
        → ValidChain c
        → toList (blocks c) ⊆ filterᵇ (λ {b → slotNumber b ≤ᵇ sl}) (toList (allBlocks t))
        → size (blocks c) ≤ size (blocks (bestChain sl t))

      -- TODO: drop `toList`?
      self-contained : ∀ (t : T) (sl : Slot)
        → toList (blocks (bestChain sl t)) ⊆ filterᵇ (λ {b → slotNumber b ≤ᵇ sl}) (toList (allBlocks t))
  ```

  ```agda
  record TreeType (T : Set) : Set₁ where

    field
      tree₀ : T
      extendTree : T → Block⋆ → T
      allBlocks : T → Blocks⋆
      bestChain : Slot → T → Chain⋆

      is-TreeType : IsTreeType tree₀ extendTree allBlocks bestChain

  open TreeType
  ```

  ## Local state

  ```agda
  record LocalState {T : Set} (blockTree : TreeType T) : Set where

    constructor ⟨_,_⟩
    field
      partyId : PartyId
      tree : T
  ```
  # Parmeterized module

  * blockTree
  * honest?
  * lottery
  * tx selection
  * hash function

  ```agda
  module _ {T : Set}
           (blockTree : TreeType T)
           (honest? : (p : PartyId) → Honesty p) -- Predicate or bool?
           (lottery : PartyId → Slot → Bool)
           (txSelection : Slot → PartyId → List Tx)
           (_♯ : Block⋆ → Hash)
           where

  ```

  ## local state

  ```agda
    Stateˡ = LocalState blockTree

    extendTreeₗ : Stateˡ → Block⋆ → Stateˡ
    extendTreeₗ ⟨ partyId , tree ⟩ b = ⟨ partyId , (extendTree blockTree) tree b ⟩

    processMsg : Message → Stateˡ → Stateˡ
    processMsg (BlockMsg b) sₗ = extendTreeₗ sₗ b

    honestRcv : List Message → Slot → Stateˡ → Stateˡ
    honestRcv msgs _ sₗ = foldr processMsg sₗ msgs

    honestCreate : Slot → List Tx → Stateˡ → List Message × Stateˡ
    honestCreate sl txs ⟨ p , tree ⟩ with lottery p sl
    ... | true = let best = (bestChain blockTree) (pred sl) tree
                     newBlock = record {
                         slotNumber = sl ;
                         creatorId = p ;
                         parentBlock = tip best ♯ ;
                         includedVotes = S.empty HashO ; -- TODO: Peras
                         leadershipProof = record { proof = emptyBS } ; -- FIXME
                         payload = txs ;
                         signature = record { signature = emptyBS } -- FIXME
                       }
                  in BlockMsg newBlock ∷ [] , ⟨ p , (extendTree blockTree) tree newBlock ⟩
    ... | false = [] , ⟨ p , tree ⟩

  ```

  ## Global state

  * clock: Current slot of the system
  * progress
  * state map
  * messages: All the messages that have been sent but not yet been delivered
  * history: All the messages that have been sent
  * execution order

  ```agda
    record Stateᵍ : Set where
      constructor ⟪_,_,_,_,_,_⟫
      field
        clock : Slot
        progress : Progress
        stateMap : Map Stateˡ
        messages : List MessageTup
        history : List Message
        execution-order : List PartyId -- TODO: List (Honesty p) ?

    open Stateᵍ public
  ```

  ### Initial global state

  ```agda
    N₀ : Stateᵍ
    N₀ = ⟪ 0 , Ready , empty , [] , [] , [] ⟫ -- FIXME: initial parties as parameter

    updateStateˡ : PartyId → Stateˡ → Stateᵍ → Stateᵍ
    updateStateˡ p sₗ N = record N { stateMap = M.insert p sₗ (stateMap N) }
  ```

  # Network

  ```agda
    fetchMsgs : PartyId → Stateᵍ → List Message × List MessageTup
    fetchMsgs p N =
        let msgs = filterᵇ ( λ {⦅ m , r , d ⦆ → ⌊ p ≟-PartyId r ⌋ ∧ ⌊ d ≟ zero ⌋ }) (messages N)
            rest = filterᵇ ( λ {⦅ m , r , d ⦆ → not (⌊ p ≟-PartyId r ⌋ ∧ ⌊ d ≟ zero ⌋) }) (messages N)
        in map ( λ { ⦅ m , _ , _ ⦆ → m } ) msgs , rest

    gossipMsg : Message → Stateᵍ → Stateᵍ
    gossipMsg m N =
      record N {
        messages = (map (λ { p → ⦅ m , p , suc zero ⦆ }) (execution-order N)) ++ messages N ;
        history = m ∷ history N
      }

    gossipMsgs : List Message → Stateᵍ → Stateᵍ
    gossipMsgs msgs N = foldr gossipMsg N msgs

    honestGossip : List Message → Stateᵍ → Stateᵍ
    honestGossip = gossipMsgs
  ```

  ## Receive

  ```agda
    data _[_]⇀_ : {p : PartyId} → Stateᵍ → Honesty p → Stateᵍ → Set where

      honestNoState : ∀ {p N}
        → lookup (stateMap N) p ≡ nothing
          -------------------------------
        → N [ Honest {p} ]⇀ N

      honest : ∀ {p N} {sₗ sₗ′ : Stateˡ} {msgs} {rest}
        → lookup (stateMap N) p ≡ just sₗ
        → (msgs , rest ) ≡ fetchMsgs p N
        → sₗ′ ≡ honestRcv msgs (clock N) sₗ
          --------------------------------
        → N [ Honest {p} ]⇀
          record N {
              stateMap = M.insert p sₗ′ (stateMap N) ;
              messages = rest
            }

      corrupt : ∀ {p N}
          ---------------------
        → N [ Corrupt {p} ]⇀ N
  ```

  <!--
  ```agda
    {-
    []⇀-does-not-modify-history : ∀ {M N p} {h : Honesty p}
      → M [ h ]⇀ N
      → history M ≡ history N
    []⇀-does-not-modify-history (honestNoState _) = refl
    []⇀-does-not-modify-history (honest _ _ _) = refl
    []⇀-does-not-modify-history corrupt = refl
    -}
  ```
  -->

  ```agda
    data _⇀_ : Stateᵍ → Stateᵍ → Set where

      Empty : ∀ {M}
        → execution-order M ≡ []
          ----------------------
        → M ⇀ M

      Cons : ∀ {M p ps} {N} {O}
        → execution-order M ≡ p ∷ ps
        → record M { execution-order = ps } [ honest? p ]⇀ N
        → N ⇀ O
          ------
        → M ⇀ O
  ```

  <!--
  ```agda
    {-
    ⇀-does-not-modify-history : ∀ {M N}
      → M ⇀ N
      → history M ≡ history N
    ⇀-does-not-modify-history (Empty _) = refl
    ⇀-does-not-modify-history (Cons _ x₁ x₂) =
      trans
        ([]⇀-does-not-modify-history x₁)
        (⇀-does-not-modify-history x₂)
    -}
  ```
  -->

  # Create

  ```agda
    data _[_]↷_ : {p : PartyId} → Stateᵍ → Honesty p → Stateᵍ → Set where

      honestNoState : ∀ {p N}
        → lookup (stateMap N) p ≡ nothing
          -------------------------------
        → N [ Honest {p} ]↷ N

      honest : ∀ {p M N} {sₗ sₗ′ : Stateˡ} {msgs}
        → (msgs , sₗ′) ≡ honestCreate (clock M) (txSelection (clock M) p) sₗ
        → N ≡ honestGossip msgs M
          ------------------------------------------------------------------
        → M [ Honest {p} ]↷
          record N {
              stateMap = M.insert p sₗ′ (stateMap N)
            }

      corrupt : ∀ {p N}
          ---------------------
        → N [ Corrupt {p} ]↷ N

  ```

  ```agda
    data _↷_ : Stateᵍ → Stateᵍ → Set where

      Empty : ∀ {M}
        → execution-order M ≡ []
          ----------------------
        → M ↷ M

      Cons : ∀ {M p ps} {N} {O}
        → execution-order M ≡ p ∷ ps
        → M [ honest? p ]↷ N
        → N ↷ O
          -------------------------------------
        → record M { execution-order = ps } ↷ O

  ```

  ## Small-step semantics for global state evolution

  ```agda
    data _↝_ : Stateᵍ → Stateᵍ → Set where

      Deliver : ∀ {M N}
        → progress M ≡ Ready
        → M ⇀ N
          ---------------------------
        → M ↝ record N {
                 progress = Delivered
               }

      Bake : ∀ {M N}
        → progress M ≡ Delivered
        → M ↷ N
          -----------------------
        → M ↝ record N {
                 progress = Baked
               }

      NextRound : ∀ {M}
        → progress M ≡ Baked
          ------------------------------
        → M ↝ record M {
                 clock = suc (clock M) ;
                 progress = Ready
               }

      PermParties : ∀ {N ps}
        → execution-order N ↭ ps
          ---------------------------
        → N ↝ record N {
                 execution-order = ps
               }

      PermMsgs : ∀ {N ms}
        → messages N ↭ ms
          --------------------
        → N ↝ record N {
                 messages = ms
               }

  ```

  ## Reflexive, transitive closure (which is big-step in the paper)

  ```agda
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
  ```

  ## hash function, collision free predicate
  -- TODO: rather use record type Hashable (requires an instance of the function)

  ```agda
    data CollisionFree (N : Stateᵍ) : Set where

      collision-free : ∀ {b₁ b₂ : Block⋆}
        → BlockMsg b₁ ∈ history N
        → BlockMsg b₂ ∈ history N
        → b₁ ♯ ≡ b₂ ♯
        → b₁ ≡ b₂
        → CollisionFree N

  {- TODO: All relation might simplify proofs

      collision-free : ∀ {b₁ b₂ : Block⋆}
        → All
          (λ { (BlockMsg b₁ , BlockMsg b₂) →
               (b₁ ♯ ≡ b₂ ♯ → b₁ ≡ b₂) })
          (cartesianProduct (history N) (history N))
        → CollisionFree N
  -}
  ```

  <!--
  ```agda
    subst′ : ∀ {A : Set} {x : A} {xs ys : List A}
      → x ∈ xs
      → xs ≡ ys
      → x ∈ ys
    subst′ {A} {x} x₁ x₂ = subst (x ∈_) x₂ x₁

    -- When the current state is collision free, the pervious state was so too

    {-
    open import Data.List.Membership.Propositional.Properties
    open import Data.Sum.Base using (_⊎_)
    open import Data.List.Relation.Binary.Subset.Propositional.Properties
    -}

    {-
    []⇀-collision-free : ∀ {M N p} {h : Honesty p}
      → CollisionFree N
      → M [ h ]⇀ N
      → CollisionFree M
    []⇀-collision-free x (honestNoState _) = x
    []⇀-collision-free x (honest x₁ x₂ x₃) = {!!}
    []⇀-collision-free x corrupt = x
    -}

    {-
    []↷-collision-free : ∀ {M N p} {h : Honesty p}
      → CollisionFree N
      → M [ h ]↷ N
      → CollisionFree M
    []↷-collision-free x (honestNoState _) = x
    []↷-collision-free (collision-free x x₁ x₂ x₃) (honest {msgs = []} _ _) = collision-free {!!} {!!} x₂ x₃ -- lottery is always false, therefore no (m ∷ msgs) case so far
    []↷-collision-free x corrupt = x

    ∷-collision-free : ∀ {cl pr sm ms hs ps p}
      → CollisionFree ⟪ cl , pr , sm , ms , hs , p ∷ ps ⟫
      → CollisionFree ⟪ cl , pr , sm , ms , hs , ps ⟫
    ∷-collision-free (collision-free x x₁ x₂ x₃) = collision-free x x₁ x₂ x₃

    prog-collision-free : ∀ {cl pr₁ pr₂ sm ms hs ps}
      → CollisionFree ⟪ cl , pr₁ , sm , ms , hs , ps ⟫
      → CollisionFree ⟪ cl , pr₂ , sm , ms , hs , ps ⟫
    prog-collision-free (collision-free x x₁ x₂ x₃) = collision-free x x₁ x₂ x₃

    ↷-collision-free : ∀ {M N}
      → CollisionFree N
      → M ↷ N
      → CollisionFree M
    ↷-collision-free x (Empty _) = x
    ↷-collision-free {M = ⟪ cl , pr , sm , ms , hs , ps ⟫} {N} n@(collision-free x x₄ x₅ x₆) (Cons {M = M} {p = p} {ps} {O = N} refl x₂ x₃) =
      let m = ↷-collision-free n x₃
          m′ = []↷-collision-free {M = ⟪ cl , pr , sm , ms , hs , p ∷ ps ⟫} m x₂
      in ∷-collision-free m′

    ↝-collision-free : ∀ {N₁ N₂ : Stateᵍ}
      → N₁ ↝ N₂
      → CollisionFree N₂
        ----------------
      → CollisionFree N₁

    ↝-collision-free (Deliver (Empty refl)) (collision-free x x₁ x₂ x₃) = collision-free x x₁ x₂ x₃
    ↝-collision-free (Deliver (Cons refl x₅ y)) (collision-free x x₁ x₂ x₃) =
      let ≡-msg = trans ([]⇀-does-not-modify-history x₅) (⇀-does-not-modify-history y)
      in collision-free (subst′ x (sym ≡-msg)) (subst′ x₁ (sym ≡-msg)) x₂ x₃
    ↝-collision-free (Bake (Empty refl)) (collision-free x x₁ x₂ x₃) = collision-free x x₁ x₂ x₃
    ↝-collision-free (Bake (Cons refl x₅ y)) n@(collision-free x x₁ x₂ x₃) =
      let m = ↷-collision-free (prog-collision-free n) y
          m′ = []↷-collision-free m x₅
      in ∷-collision-free m′
    ↝-collision-free NextRound (collision-free x x₁ x₂ x₃) = collision-free x x₁ x₂ x₃
    ↝-collision-free (PermParties _) (collision-free x x₁ x₂ x₃) = collision-free x x₁ x₂ x₃
    ↝-collision-free (PermMsgs p) (collision-free x x₁ x₂ x₃) = collision-free x x₁ x₂ x₃

    -- When the current state is collision free, previous states were so too

    ↝⋆-collision-free : ∀ {N₁ N₂ : Stateᵍ}
      → N₁ ↝⋆ N₂
      → CollisionFree N₂
        ----------------
      → CollisionFree N₁
    ↝⋆-collision-free (_ ∎) N = N
    ↝⋆-collision-free (_ ↝⟨ N₁↝N₂ ⟩ N₂↝⋆N₃) N₃ =
      ↝-collision-free N₁↝N₂ (↝⋆-collision-free N₂↝⋆N₃ N₃)

    -}
  ```
  -->
