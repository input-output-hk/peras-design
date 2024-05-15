```agda
module Praos.SmallStep where
```

<!--
```agda
open import Data.Fin using (Fin; zero; suc) renaming (pred to decr)
open import Data.List using (List; _∷_; []; _++_; cartesianProduct; filter; length; map)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Any using (Any; _─_; _∷=_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_≤?_; _≤_; suc)
open import Data.Nat.Properties using (≤-totalOrder)
open import Data.Product using (∃-syntax; _×_; _,_; uncurry)
open import Function using (_∘_; id; _$_; flip)
open import Relation.Binary.Bundles using (StrictTotalOrder)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym; subst; trans)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary.Negation using (contradiction; contraposition)

open import Data.List.Extrema (≤-totalOrder) using (argmax)

open import Praos.Chain
open import Praos.Crypto
open import Praos.Block

open import Data.Tree.AVL.Map PartyIdO as M using (Map; lookup; insert; empty)
open import Data.List.Relation.Binary.Subset.Propositional {A = Block} using (_⊆_)

open Honesty public
open MembershipProof public
open Signature public
open Party
```
-->

# Small-step semantics

The small-step semantics define the possible evolution of the global state of the system
under the Praos protocol modelling honest and adversary parties.

The goal is to show *safety* and *liveness* for the protocol.

Reference: Formalizing Nakamoto-Style Proof of Stake, Søren Eller Thomsen and Bas Spitters

Messages for sending and receiving blocks
```agda
data Message : Set where
  BlockMsg : Block → Message
```
<!--
```agda
Message-injective : ∀ {b₁ b₂}
  → BlockMsg b₁ ≡ BlockMsg b₂
  → b₁ ≡ b₂
Message-injective refl = refl
```
```agda
Message-injective′ : ∀ {b₁ b₂}
  → b₁ ≢ b₂
  → BlockMsg b₁ ≢ BlockMsg b₂
Message-injective′ = contraposition Message-injective
```
-->
Messages can be delayed by an adversary. Delay is either 0, 1

```agda
Delay = Fin 2
```
Messages are put into an envelope which is assigned to a given party and is defined with
a delay.
```agda
record Envelope : Set where
  constructor ⦅_,_,_,_⦆
  field
    partyId : PartyId
    honesty : Honesty partyId
    message : Message
    delay : Delay

open Envelope
```
<!--
```agda
⦅⦆-injective : ∀ {e₁ e₂}
  → e₁ ≡ e₂
  → partyId e₁ ≡ partyId e₂
⦅⦆-injective refl = refl
```
```agda
⦅⦆-injective₃ : ∀ {e₁ e₂}
  → e₁ ≡ e₂
  → message e₁ ≡ message e₂
⦅⦆-injective₃ refl = refl
```
```agda
⦅⦆-injective′ : ∀ {e₁ e₂}
  → partyId e₁ ≢ partyId e₂
  → e₁ ≢ e₂
⦅⦆-injective′ = contraposition ⦅⦆-injective
```
```agda
⦅⦆-injective₃′ : ∀ {e₁ e₂}
  → message e₁ ≢ message e₂
  → e₁ ≢ e₂
⦅⦆-injective₃′ = contraposition ⦅⦆-injective₃
```
-->
<!--
```agda
-- We introduce the relation ≐ to denote that two lists have the same elements
open import Relation.Binary.Core using (Rel)
_≐_ : Rel (List Block) _
P ≐ Q = (P ⊆ Q) × (Q ⊆ P)
```
-->

block₀ denotes the genesis block that is passed in as a module parameter.

```agda
module _ {block₀ : Block}
         {IsSlotLeader : PartyId → Slot → LeadershipProof → Set}
         {IsBlockSignature : Block → Signature → Set}
         ⦃ _ : Hashable Block ⦄
         ⦃ _ : Hashable (List Tx) ⦄
         where
```
  Bringing the hash function into scope

```agda
  open Hashable ⦃...⦄
```
  The block tree, resp. the validity of the chain is defined with respect of the
  parameters.


## BlockTree

```agda
  record IsTreeType {tT : Set}
                    (tree₀ : tT)
                    (extendTree : tT → Block → tT)
                    (allBlocks : tT → List Block)
                    (bestChain : Slot → tT → Chain)
         : Set₁ where

    allBlocksUpTo : Slot → tT → List Block
    allBlocksUpTo sl t = filter ((_≤? sl) ∘ slotNumber) (allBlocks t)

    field
```
```agda
      instantiated :
        allBlocks tree₀ ≡ block₀ ∷ []

      extendable : ∀ (t : tT) (b : Block)
        → allBlocks (extendTree t b) ≐ (b ∷ allBlocks t)

      valid : ∀ (t : tT) (sl : Slot)
        → ValidChain {block₀} {IsSlotLeader} {IsBlockSignature} (bestChain sl t)

      optimal : ∀ (c : Chain) (t : tT) (sl : Slot)
        → let b = bestChain sl t
          in
          ValidChain {block₀} {IsSlotLeader} {IsBlockSignature} c
        → c ⊆ allBlocksUpTo sl t
        → length c ≤ length b

      self-contained : ∀ (t : tT) (sl : Slot)
        → bestChain sl t ⊆ allBlocksUpTo sl t
```
The block tree type

```agda
  record TreeType (T : Set) : Set₁ where

    field
      tree₀ : T
      extendTree : T → Block → T
      allBlocks : T → List Block
      bestChain : Slot → T → Chain

      is-TreeType : IsTreeType
                      tree₀ extendTree allBlocks bestChain

    tipBest : Slot → T → Block
    tipBest sl t = tip (valid is-TreeType t sl) where open IsTreeType

  open TreeType
```
## Local state

```agda
  record LocalState {A : Set} (blockTree : TreeType A) : Set where
    constructor ⟪_⟫
    field
      tree : A

  open LocalState
```
<!--
```agda
  ⟪⟫-injective : ∀  {A : Set} {blockTree : TreeType A} {a b : LocalState blockTree}
    → a ≡ b
    → tree a ≡ tree b
  ⟪⟫-injective refl = refl
```
-->
# Parameterized module

  * blockTree
  * slot leader predicate
  * voting committee membership predicate
  * tx selection
  * The list of parties
  * AdversarialState₀ is the initial adversarial state


```agda
  module _ {tT : Set}
           {blockTree : TreeType tT}
           {AdversarialState : Set}
           {adversarialsState₀ : AdversarialState}
           {txSelection : Slot → PartyId → List Tx}
           {parties : Parties}

           where
```
The local state initialized with the block tree

```agda
    Stateˡ = LocalState blockTree
```
### State update

Updating the local state upon receiving a message: Blocks received as messages
are delegated to the block tree.

```agda
    data _[_]→_ : Stateˡ → Message → Stateˡ → Set where

      BlockReceived : ∀ {b t}
          ----------------------------
        → ⟪ t ⟫ [ BlockMsg b ]→
          ⟪ extendTree blockTree t b ⟫
```
## Global state

```agda
    record Stateᵍ : Set where
      constructor ⟦_,_,_,_,_⟧
      field
```
The global state consists of the following fields:

* Current slot of the system
```agda
        clock : Slot
```
* Map with local state per party
```agda
        stateMap : Map Stateˡ
```
* All the messages that have been sent but not yet been delivered
```agda
        messages : List Envelope
```
* All the messages that have been sent
```agda
        history : List Message
```
* Adversarial state
```agda
        adversarialState : AdversarialState
```
Progress
```agda
    Delivered : Stateᵍ → Set
    Delivered = All (λ { z → delay z ≢ zero }) ∘ messages where open Stateᵍ
```
Updating global state
```agda
    _,_,_,_↑_ : Message → Delay → PartyId → Stateˡ → Stateᵍ → Stateᵍ
    m , d , p , l ↑ ⟦ c , s , ms , hs , as ⟧ =
      ⟦ c , insert p l s , map (uncurry ⦅_,_, m , d ⦆) parties ++ ms , m ∷ hs , as ⟧
```
Ticking the global clock
```agda
    tick : Stateᵍ → Stateᵍ
    tick M =
      record M {
        clock = suc (clock M) ;
        messages = map (λ where
          e → record e { delay = decr (delay e) }) (messages M)
      }
      where open Stateᵍ
```
## Receive

A party receives messages from the global state by fetching messages assigned to the party,
updating the local block tree and putting the local state back into the global state.

```agda
    data _⊢_[_]⇀_ : {p : PartyId} → Honesty p → Stateᵍ → Message → Stateᵍ → Set where
```
An honest party consumes a message from the global message buffer and updates the
the local state
```agda
      honest : ∀ {p} {lₚ lₚ′} {m} {c s ms hs as}
        → lookup s p ≡ just lₚ
        → (m∈ms : ⦅ p , Honest , m , zero ⦆ ∈ ms)
        → lₚ [ m ]→ lₚ′
          ----------------------------------------
        → Honest {p} ⊢
          ⟦ c
          , s
          , ms
          , hs
          , as
          ⟧ [ m ]⇀
          ⟦ c
          , insert p lₚ′ s
          , ms ─ m∈ms
          , hs
          , as
          ⟧
```
An adversarial party might delay a message
```agda
      corrupt : ∀ {p c s ms hs as as′} {m}
        → (m∈ms : ⦅ p , Corrupt , m , zero ⦆ ∈ ms)
          -----------------------------------------
        → Corrupt {p} ⊢
          ⟦ c
          , s
          , ms
          , hs
          , as
          ⟧ [ m ]⇀
          ⟦ c
          , s -- TODO: insert p lₚ s
          , m∈ms ∷= ⦅ p , Corrupt , m , suc zero ⦆
          , hs
          , as′
          ⟧
```
## Create

A party can create a new block by adding it to the local block tree and gossiping the
block creation messages to the other parties. Block creation is possilble, if
  * the block signature is correct
  * the party is the slot leader

Block creation updates the party's local state and for all other parties a message
is added to be consumed immediately.
```agda
    data _⊢_↷_ : {p : PartyId} → Honesty p → Stateᵍ → Stateᵍ → Set where
```
```agda
      honest : ∀ {p} {t} {M} {prf} {sig} {block}
        → let open Stateᵍ M
              txs = txSelection clock p
              b = record
                    { slotNumber = clock
                    ; creatorId = p
                    ; parentBlock = hash $ tipBest blockTree clock t
                    ; leadershipProof = prf
                    ; bodyHash = blockHash
                        record { blockHash = hash txs
                               ; payload = txs
                               }
                    ; signature = sig
                    }
              lₚ = ⟪ extendTree blockTree t b ⟫
          in
          block ≡ b
        → lookup stateMap p ≡ just ⟪ t ⟫
        → IsBlockSignature b sig
        → IsSlotLeader p clock prf
          --------------------------------------
        → Honest {p} ⊢
            M ↷ (BlockMsg b , zero , p , lₚ ↑ M)
```
Rather than creating a delayed block, an adversary can honestly create it and delay the message

# Small-step semantics

The small-step semantics describe the evolution of the global state.

```agda
    data _↝_ : Stateᵍ → Stateᵍ → Set where

      Deliver : ∀ {M N p} {h : Honesty p} {m}
        → h ⊢ M [ m ]⇀ N
          --------------
        → M ↝ N

      CreateBlock : ∀ {M N p} {h : Honesty p}
        → h ⊢ M ↷ N
          ---------
        → M ↝ N

      NextSlot : ∀ {M}
        → Delivered M
          -----------
        → M ↝ tick M
```

## Reflexive, transitive closure

In the paper mentioned above this is big-step semantics.

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
<!--
### Composition
```agda
    ↝⋆∘↝⋆ : ∀ {M N O}
      → M ↝⋆ N
      → N ↝⋆ O
      → M ↝⋆ O
    ↝⋆∘↝⋆ (_ ∎) M↝⋆O = M↝⋆O
    ↝⋆∘↝⋆ {M} (_ ↝⟨ M↝M₁ ⟩ M₁↝⋆N) N↝⋆O = (_ ↝⟨ M↝M₁ ⟩ (↝⋆∘↝⋆ M₁↝⋆N N↝⋆O))
```
### Post-composition
```agda
    ↝∘↝⋆ : ∀ {M N O}
      → M ↝⋆ N
      → N ↝ O
      → M ↝⋆ O
    ↝∘↝⋆ {M} {N} {O} (_ ∎) N↝O = M ↝⟨ N↝O ⟩ (O ∎)
    ↝∘↝⋆ {M} (_ ↝⟨ M↝M₁ ⟩ M₁↝⋆N) N↝O = M ↝⟨ M↝M₁ ⟩ (↝∘↝⋆ M₁↝⋆N N↝O)
```
-->
# Collision free predicate

<!--
```agda
    open Stateᵍ
```
-->

Rather than assuming a global axiom on the injectivity of the hash function
or that any reachable state is collision-free, there is a predicate assuming
that there are no hash collisions during the execution of the protocol.

```agda
    data CollisionFree (N : Stateᵍ) : Set where

      collision-free : ∀ {b₁ b₂ : Block}
        → All
          (λ { (m₁ , m₂) → m₁ ≡ BlockMsg b₁ → m₂ ≡ BlockMsg b₂ →
               (hash b₁ ≡ hash b₂ → b₁ ≡ b₂) })
          (cartesianProduct (history N) (history N))
        → CollisionFree N
```

<!--
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

    []-hist-common-prefix : ∀ {M N p} {h : Honesty p} {m}
      → h ⊢ M [ m ]⇀ N
      → history M ⊆ₘ history N
    []-hist-common-prefix (honest _ _ _) x = x
    []-hist-common-prefix (corrupt _) x = x

    []⇀-collision-free : ∀ {M N p} {h : Honesty p} {m}
      → CollisionFree N
      → h ⊢ M [ m ]⇀ N
      → CollisionFree M
    []⇀-collision-free (collision-free {b₁} {b₂} x) (honest _ _ _) = collision-free {b₁ = b₁} {b₂ = b₂} x
    []⇀-collision-free (collision-free {b₁} {b₂} x) (corrupt _) = collision-free {b₁ = b₁} {b₂ = b₂} x

    -- Create

    []↷-hist-common-prefix : ∀ {M N p} {h : Honesty p}
      → h ⊢ M ↷ N
      → history M ⊆ₘ history N
    []↷-hist-common-prefix {M} (honest {block = b} refl _ _ _) = xs⊆x∷xs (history M) (BlockMsg b)

    []↷-collision-free : ∀ {M N p} {h : Honesty p}
      → CollisionFree N
      → h ⊢ M ↷ N
      → CollisionFree M
    []↷-collision-free cf-N M[]↷N = collision-free-resp-⊇ cf-N ([]↷-hist-common-prefix M[]↷N)
```
-->

## Properties

When the current state is collision free, the pervious state was so too

```agda
    ↝-collision-free : ∀ {N₁ N₂ : Stateᵍ}
      → N₁ ↝ N₂
      → CollisionFree N₂
        ----------------
      → CollisionFree N₁
```
<!--
```agda
    ↝-collision-free (Deliver x) cf-N₂ = []⇀-collision-free cf-N₂ x
    ↝-collision-free (CreateBlock x) cf-N₂ =  []↷-collision-free cf-N₂ x
    ↝-collision-free (NextSlot _) (collision-free x) = collision-free x
```
-->

When the current state is collision free, previous states were so too

```agda
    ↝⋆-collision-free : ∀ {N₁ N₂ : Stateᵍ}
      → N₁ ↝⋆ N₂
      → CollisionFree N₂
        ----------------
      → CollisionFree N₁
```
<!--
```agda
    ↝⋆-collision-free (_ ∎) N = N
    ↝⋆-collision-free (_ ↝⟨ N₁↝N₂ ⟩ N₂↝⋆N₃) N₃ =
      ↝-collision-free N₁↝N₂ (↝⋆-collision-free N₂↝⋆N₃ N₃)
```
-->

# Forging free predicate

Signatures are not modelled explicitly. Instead we assume that the adversary cannot send any
block with the `creatorId` of an honest party that is not already in the block history.

```agda
    data ForgingFree (N : Stateᵍ) : Set where

      forging-free : ∀ {M : Stateᵍ} {b} {p}
        → Corrupt {p} ⊢ M ↷ N
        → All (λ { m → (m ≡ BlockMsg b × HonestBlock b)
            → m ∈ history M }) (history N)
        → ForgingFree N
```
