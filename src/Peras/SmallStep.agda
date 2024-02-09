module Peras.SmallStep where

open import Data.Bool
open import Data.List using (List; all; foldr; _∷_; []; _++_)
open import Data.Maybe
open import Data.Nat using (suc; pred)
open import Data.Product using (_,_; _×_)
open import Function.Base using (_∘_; id)
open import Level using (0ℓ)
open import Relation.Binary using (StrictTotalOrder)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)

open import Peras.Chain using (Chain⁺)
open import Peras.Crypto using (Hash; HashO; hash; emptyBS)
open import Peras.Block using (PartyId; PartyIdO; Block⁺; Slot; Tx)

open import Data.Tree.AVL.Sets as S renaming (⟨Set⟩ to set) using ()

open import Data.Tree.AVL.Map PartyIdO using (Map; lookup; insert; empty)

{-
  Formalizing Nakamoto-Style Proof of Stake
  Søren Eller Thomsen and Bas Spitters
-}

data Honesty : Set where
  Honest : Honesty
  Corrupt : Honesty

record IsTreeType {T : Set}
                  (tree₀ : T)
                  (extendTree : T → Block⁺ → T)
                  (allBlocks : T → List Block⁺)
                  (bestChain : Slot → T → Chain⁺)
       : Set where

  field -- TODO: * missing fields
        --       * use proper relation instead of ≡
    -- instantiated
    extendable : ∀ (t : T) (b : Block⁺) → allBlocks (extendTree t b) ≡ (allBlocks t) ++ (b ∷ [])
    -- valid
    -- optimal
    -- self-contained

record TreeType (T : Set) : Set where

  field
    tree₀ : T
    extendTree : T → Block⁺ → T
    allBlocks : T → List Block⁺
    bestChain : Slot → T → Chain⁺

    is-TreeType : IsTreeType tree₀ extendTree allBlocks bestChain

open TreeType

record LocalState {T : Set} : Set where

  constructor ⟨_,_,_⟩

  field
    partyId : PartyId
    tT : TreeType T
    tree : T

module _ {T : Set} (honest? : PartyId → Honesty) where

  Stateₗ = LocalState {T}

  data Progress : Set where
    Ready : Progress
    Delivered : Progress
    Baked : Progress

  data Message : Set where
    BlockMsg : Block⁺ → Message

  extendTreeₗ : Stateₗ → Block⁺ → Stateₗ
  extendTreeₗ ⟨ partyId , tT , tree ⟩ b = ⟨ partyId , tT , (extendTree tT) tree b ⟩

  processMsg : Message → Stateₗ → Stateₗ
  processMsg (BlockMsg b) sₗ = extendTreeₗ sₗ b

  honestRcv : List Message → Slot → Stateₗ → Stateₗ
  honestRcv msgs _ sₗ = foldr processMsg sₗ msgs

  lottery : PartyId → Slot → Bool
  lottery _ _ = false -- FIXME

  honestCreate : Slot → List Tx → Stateₗ → List Message × Stateₗ
  honestCreate sl txs ⟨ p , tT , tree ⟩ with lottery p sl
  ... | true = let best = (bestChain tT) (pred sl) tree
                   parent = record { hash = emptyBS } -- FIXME
                   newBlock = record {
                       slotNumber = sl ;
                       creatorId = p ;
                       parentBlock = parent ;
                       includedVotes = S.empty HashO ;
                       leadershipProof = record { proof = emptyBS } ;
                       payload = txs ;
                       signature = record { signature = emptyBS }
                     }
                in BlockMsg newBlock ∷ [] , ⟨ p , tT , (extendTree tT) tree newBlock ⟩
  ... | false = [] , ⟨ p , tT , tree ⟩

  -- global state

  record GlobalState : Set where
    constructor ⟪_,_,_,_,_⟫
    field
      slot : Slot
      progress : Progress
      stateMap : Map Stateₗ
      messages : List Message
      execution-order : List PartyId

  open GlobalState

  -- network

  fetchMsgs : PartyId → GlobalState → List Message × GlobalState
  fetchMsgs _ N = (messages N , N) -- FIXME: * implement network model with delays
                                   --        * filter messages

  -- initial state

  N₀ : GlobalState
  N₀ = ⟪ 0 , Ready , empty , [] , [] ⟫ -- TODO: initial parties

  incrementSlot : Slot → Slot
  incrementSlot = suc

  permParties : List PartyId → List PartyId
  permParties = id -- FIXME: permute

  permMessages : List Message → List Message
  permMessages = id -- FIXME: permute

  updateStateₗ : PartyId → Stateₗ → GlobalState → GlobalState
  updateStateₗ p sₗ N = record N { stateMap = insert p sₗ (stateMap N) }

  -- receive

  party↓ : PartyId → GlobalState → GlobalState
  party↓ p N with lookup (stateMap N) p | honest? p
  ... | just sₗ | Honest = let (msgs , N⁺) = fetchMsgs p N
                               sₗ⁺ = honestRcv msgs (slot N) sₗ
                           in updateStateₗ p sₗ⁺ N⁺
  ... | just sₗ | Corrupt = N -- FIXME: implement adversary
  ... | nothing | _ = N

  -- create

  party↷ : PartyId → GlobalState → GlobalState
  party↷ p N with lookup (stateMap N) p | honest? p
  ... | just sₗ | Honest = let (msgs , sₗ⁺) = honestCreate (slot N) [] sₗ
                           -- FIXME: gossip msgs
                           in updateStateₗ p sₗ⁺ N
  ... | just sₗ | Corrupt = N -- FIXME: implement adversary
  ... | nothing | _ = N


  data _↝_ : GlobalState → GlobalState → Set where

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
      → ⟪ s , Baked , sm , ms , ps ⟫ ↝ ⟪ incrementSlot s , Ready , sm , ms , ps ⟫

    PermParties : ∀ {s p sm ms ps}
      → ⟪ s , p , sm , ms , ps ⟫ ↝ ⟪ s , p , sm , ms , permParties ps ⟫

    PermMsgs : ∀ {s p sm ms ps}
      → ⟪ s , p , sm , ms , ps ⟫ ↝ ⟪ s , p , sm , permMessages ms , ps ⟫

  -- reflexive, transitive closure (which is big-step in the paper)

  infix  2 _↝⋆_
  infixr 2 _↝⟨_⟩_
  infix  3 _∎

  data _↝⋆_ : GlobalState → GlobalState → Set where

    _∎ : ∀ M
        -------
      → M ↝⋆ M

    _↝⟨_⟩_ : ∀ L {M N}
      → L ↝ M
      → M ↝⋆ N
        ------
      → L ↝⋆ N
