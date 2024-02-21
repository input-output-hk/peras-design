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

open import Peras.Chain using (Chain⋆; ValidChain; Vote)
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
   VoteMsg : Vote Hash → Message


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
  # Parameterized module

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

  ## Local state

  ```agda
    Stateˡ = LocalState blockTree

    extendTreeₗ : Stateˡ → Block⋆ → Stateˡ
    extendTreeₗ ⟨ partyId , tree ⟩ b = ⟨ partyId , (extendTree blockTree) tree b ⟩

    processMsg : Message → Stateˡ → Stateˡ
    processMsg (BlockMsg b) sₗ = extendTreeₗ sₗ b
    processMsg (VoteMsg v) sₗ = sₗ -- TODO

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

  ## Collision free predicate

  ```agda
    data CollisionFree (N : Stateᵍ) : Set where

{-
      collision-free : ∀ {b₁ b₂ : Block⋆}
        → BlockMsg b₁ ∈ history N
        → BlockMsg b₁ ∈ history N
        → b₁ ♯ ≡ b₂ ♯
        → b₁ ≡ b₂
        → CollisionFree N
-}

      collision-free : ∀ {b₁ b₂ : Block⋆}
        → All
          (λ { (m₁ , m₂) → m₁ ≡ BlockMsg b₁ → m₂ ≡ BlockMsg b₂ →
               (b₁ ♯ ≡ b₂ ♯ → b₁ ≡ b₂) })
          (cartesianProduct (history N) (history N))
        → CollisionFree N

  ```
  When the current state is collision free, the pervious state was so too

  ```agda
    open import Data.List.Relation.Binary.Subset.Propositional.Properties
    open import Data.List.Relation.Binary.Subset.Propositional {A = Message} using (_⊇_) renaming (_⊆_ to _⊆ₘ_)
    open import Data.List.Relation.Binary.Subset.Propositional {A = Message × Message} renaming (_⊇_ to _⊇ₓ_ ; _⊆_ to _⊆ₘₓ_)

    open import Data.List.Membership.Propositional.Properties

    ⊆→⊆-cartesianProduct : ∀ {a b} → a ⊆ₘ b → cartesianProduct a a ⊆ₘₓ cartesianProduct b b
    ⊆→⊆-cartesianProduct {a} a⊆b x =
      let x₁ , x₂ = ∈-cartesianProduct⁻ a a x
       in ∈-cartesianProduct⁺ (a⊆b x₁) (a⊆b x₂)

    collision-free-resp-⊇ : ∀ {M N}
      → CollisionFree N
      → history N ⊇ history M
      → CollisionFree M
    collision-free-resp-⊇ (collision-free {b₁} {b₂} cf) x =
      collision-free {b₁ = b₁} {b₂ = b₂} (All-resp-⊇ (⊆→⊆-cartesianProduct x) cf)

    -- Receive

    []-hist-common-prefix : ∀ {M N p} {h : Honesty p}
      → M [ h ]⇀ N
      → history M ⊆ₘ history N
    []-hist-common-prefix (honestNoState _) x = x
    []-hist-common-prefix (honest _ _ _) x = x
    []-hist-common-prefix corrupt x = x

    []⇀-collision-free : ∀ {M N p} {h : Honesty p}
      → CollisionFree N
      → M [ h ]⇀ N
      → CollisionFree M
    []⇀-collision-free cf-N (honestNoState _) = cf-N
    []⇀-collision-free (collision-free {b₁} {b₂} x) (honest _ _ _) = collision-free {b₁ = b₁} {b₂ = b₂} x
    []⇀-collision-free cf-N corrupt = cf-N

    ⇀-hist-common-prefix : ∀ {M N}
      → M ⇀ N
      → history M ⊆ₘ history N
    ⇀-hist-common-prefix (Empty _) x = x
    ⇀-hist-common-prefix (Cons refl x₂ x₃) = ⊆-trans ([]-hist-common-prefix x₂) (⇀-hist-common-prefix x₃)

    ⇀-collision-free : ∀ {M N}
      → CollisionFree N
      → M ⇀ N
      → CollisionFree M
    ⇀-collision-free cf-N M⇀N = collision-free-resp-⊇ cf-N (⇀-hist-common-prefix M⇀N)

    -- Create

    -- TODO: implement Gossip data type
    postulate
      hist-honestGossipMsgs : ∀ {M N} {msgs}
        → N ≡ honestGossip msgs M
        → history N ⊇ history M

    []↷-hist-common-prefix : ∀ {M N p} {h : Honesty p}
      → M [ h ]↷ N
      → history M ⊆ₘ history N
    []↷-hist-common-prefix (honestNoState _) x = x
    []↷-hist-common-prefix (honest {msgs = msgs} x x₁) = hist-honestGossipMsgs {msgs = msgs} x₁
    []↷-hist-common-prefix corrupt x = x

    ↷-hist-common-prefix : ∀ {M N}
      → M ↷ N
      → history M ⊆ₘ history N
    ↷-hist-common-prefix (Empty _) x = x
    ↷-hist-common-prefix (Cons refl x₂ x₃) = ⊆-trans ([]↷-hist-common-prefix x₂) (↷-hist-common-prefix x₃)

    []↷-collision-free : ∀ {M N p} {h : Honesty p}
      → CollisionFree N
      → M [ h ]↷ N
      → CollisionFree M
    []↷-collision-free cf-N M[]↷N = collision-free-resp-⊇ cf-N ([]↷-hist-common-prefix M[]↷N)

    ↷-collision-free : ∀ {M N}
      → CollisionFree N
      → M ↷ N
      → CollisionFree M
    ↷-collision-free cf-N (Empty _) = cf-N
    ↷-collision-free cf-N M↷N = collision-free-resp-⊇ cf-N (↷-hist-common-prefix M↷N)

    ↝-collision-free : ∀ {N₁ N₂ : Stateᵍ}
      → N₁ ↝ N₂
      → CollisionFree N₂
        ----------------
      → CollisionFree N₁
    ↝-collision-free (Deliver _ (Empty _)) (collision-free {b₁} {b₂} cf) = collision-free {b₁ = b₁} {b₂ = b₂} cf
    ↝-collision-free (Deliver refl (Cons refl x₁ x₂)) n@(collision-free {b₁} {b₂} cf) =
      let cf-N = ⇀-collision-free (collision-free {b₁ = b₁} {b₂ = b₂} cf) x₂
      in uncons-collision-free ([]⇀-collision-free cf-N x₁)
      where
        uncons-collision-free : ∀ {cl pr sm ms hs ps p}
          → CollisionFree ⟪ cl , pr , sm , ms , hs , ps ⟫
          → CollisionFree ⟪ cl , pr , sm , ms , hs , p ∷ ps ⟫
        uncons-collision-free (collision-free {b₁} {b₂} x) = collision-free {b₁ = b₁} {b₂ = b₂} x
    ↝-collision-free (Bake _ (Empty x₁)) (collision-free {b₁} {b₂} cf) = collision-free {b₁ = b₁} {b₂ = b₂} cf
    ↝-collision-free (Bake x (Cons refl x₁ x₂)) (collision-free {b₁} {b₂} cf) =
      let cf-N = ↷-collision-free (collision-free {b₁ = b₁} {b₂ = b₂} cf) x₂
      in cons-collision-free ([]↷-collision-free cf-N x₁)
      where
          cons-collision-free : ∀ {cl pr sm ms hs ps p}
            → CollisionFree ⟪ cl , pr , sm , ms , hs , p ∷ ps ⟫
            → CollisionFree ⟪ cl , pr , sm , ms , hs , ps ⟫
          cons-collision-free (collision-free {b₁} {b₂} cf) = collision-free {b₁ = b₁} {b₂ = b₂} cf
    ↝-collision-free (NextRound _) (collision-free {b₁} {b₂} cf) = collision-free {b₁ = b₁} {b₂ = b₂} cf
    ↝-collision-free (PermParties _) (collision-free {b₁} {b₂} cf) = collision-free {b₁ = b₁} {b₂ = b₂} cf
    ↝-collision-free (PermMsgs _) (collision-free {b₁} {b₂} cf) = collision-free {b₁ = b₁} {b₂ = b₂} cf

    -- When the current state is collision free, previous states were so too

    ↝⋆-collision-free : ∀ {N₁ N₂ : Stateᵍ}
      → N₁ ↝⋆ N₂
      → CollisionFree N₂
        ----------------
      → CollisionFree N₁
    ↝⋆-collision-free (_ ∎) N = N
    ↝⋆-collision-free (_ ↝⟨ N₁↝N₂ ⟩ N₂↝⋆N₃) N₃ =
      ↝-collision-free N₁↝N₂ (↝⋆-collision-free N₂↝⋆N₃ N₃)
  ```
