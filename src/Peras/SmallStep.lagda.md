```agda
module Peras.SmallStep where
```

<!--
```agda
open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.Fin using (Fin; fromℕ; zero; suc)
open import Data.Fin.Properties as Fin using ()
open import Data.List as List using (List; all; foldr; _∷_; []; _++_; filter; filterᵇ; map; cartesianProduct; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
open import Data.Maybe using (just; nothing)
open import Data.Nat using (suc; pred; _≤_; _≤ᵇ_; ℕ; _+_)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
open import Function.Base using (_∘_; id)
open import Relation.Binary.Bundles using (StrictTotalOrder)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; subst; trans)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Peras.Chain using (Chain; tip; Vote; RoundNumber; _∻_; ValidChain)
open import Peras.Crypto using (Hashable; emptyBS; MembershipProof; Signature)
open import Peras.Block using (PartyId; PartyIdO; Block; Slot; slotNumber; Tx; Honesty)
open import Peras.Message renaming (Message to Msg)
open import Peras.Params

open import Data.Tree.AVL.Map PartyIdO as M using (Map; lookup; insert; empty)
open import Data.List.Relation.Binary.Subset.Propositional {A = Block} using (_⊆_)

open Chain public
open Honesty public
open MembershipProof public
open Signature public
open RoundNumber public
open Vote
```
-->

# Small-step semantics

The small-step semantics define the possible evolution of the global state of the system
under the Peras protocol modelling honest and adversary parties.

The goal is to show *safety* and *liveness* for the protocol.

Reference: Formalizing Nakamoto-Style Proof of Stake, Søren Eller Thomsen and Bas Spitters

### Progress

In addition to the formalization in the paper, for the Peras protocol there is a new global
state `Voted` indicating that all honest parties eligible to vote have cast a vote.

```agda
data Progress : Set where
   Ready : Progress
   Delivered : Progress
   Voted : Progress
   Baked : Progress
```

Messages are put into an envelope

```agda
Message = Msg Block

record Envelope : Set where
  constructor ⦅_,_,_⦆
  field
    msg : Message
    rcv : PartyId
    cd : Fin 3
```

We introduce the relation ≐ to denote that two lists have the same elements

```agda
open import Relation.Binary.Core using (Rel)
_≐_ : Rel (List Block) _
P ≐ Q = (P ⊆ Q) × (Q ⊆ P)
```

block₀ denotes the genesis block that is passed in as a module parameter

```agda
module _ {block₀ : Block}
         ⦃ _ : Hashable Block ⦄
         ⦃ _ : Hashable (Vote Block) ⦄
         ⦃ _ : Params ⦄
         where
```
  Bringing the hash function into scope

```agda
  open Hashable ⦃...⦄
```
  The block tree, resp. the validity of the chain is defined with respect of the
  parameters.

```agda
  open Params ⦃...⦄
```
## BlockTree

```agda
  record IsTreeType {T : Set}
                    (tree₀ : T)
                    (extendTree : T → Block → T)
                    (allBlocks : T → List Block)
                    (bestChain : Slot → T → Chain)
                    (addVote : T → Vote Block → T)
         : Set₁ where
    field
```
Properties that must hold with respect to blocks and votes

```agda
      instantiated :
        allBlocks tree₀ ≡ block₀ ∷ []

      extendable : ∀ (t : T) (b : Block)
        → allBlocks (extendTree t b) ≐ (b ∷ allBlocks t)

      valid : ∀ (t : T) (sl : Slot)
        → ValidChain {block₀} (bestChain sl t)

      optimal : ∀ (c : Chain) (t : T) (sl : Slot)
        → ValidChain {block₀} c
        → blocks c ⊆ filterᵇ (λ {b → slotNumber b ≤ᵇ sl}) (allBlocks t)
        → length (blocks c) ≤ length (blocks (bestChain sl t))

      self-contained : ∀ (t : T) (sl : Slot)
        → blocks (bestChain sl t) ⊆ filterᵇ (λ {b → slotNumber b ≤ᵇ sl}) (allBlocks t)
```
The block tree type

```agda
  record TreeType (T : Set) : Set₁ where

    field
      tree₀ : T
      extendTree : T → Block → T
      allBlocks : T → List Block
      bestChain : Slot → T → Chain

      addVote : T → Vote Block → T
      danglingVotes : T → List (Vote Block)

      is-TreeType : IsTreeType
                      tree₀ extendTree allBlocks bestChain
                      addVote

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
  * honesty?
  * slot leader computable predicate
  * tx selection
  * hash function

```agda
  module _ {T : Set}
           {blockTree : TreeType T}
           {honest? : (p : PartyId) → Honesty p} -- Predicate or bool?
           {isSlotLeader : PartyId → Slot → Bool}
           {txSelection : Slot → PartyId → List Tx}
           where
```
The local state initialized with the block tree

```agda
    Stateˡ = LocalState blockTree
```
Honestly updating the local state upon receiving a message

```agda
    honestReceive : List Message → Stateˡ → Stateˡ
    honestReceive msg s = foldr receive s msg
      where
        receive : Message → Stateˡ → Stateˡ
        receive (SomeBlock b) ⟨ p , t ⟩ = ⟨ p , (extendTree blockTree) t b ⟩
        receive (NewChain c) s = s -- TODO
        receive (SomeVote v) ⟨ p , t ⟩ = ⟨ p , (addVote blockTree) t v ⟩
        receive (NextSlot _) s = s -- TODO
```
Honestly creating a block

```agda
    honestCreate : Slot → RoundNumber → List Tx → Stateˡ → Message × Stateˡ
    honestCreate sl (record { roundNumber = r }) txs ⟨ p , tree ⟩ =
      let best = (bestChain blockTree) (pred sl) tree
          votes = filterᵇ (λ { v → r ≤ᵇ ((roundNumber (votingRound v)) + L) } ) ((danglingVotes blockTree) tree) -- TODO: check expired, preferred chain, equivocation
          newBlock =
            record {
              slotNumber = sl ;
              creatorId = p ;
              parentBlock = hash (tip best) ;
              includedVotes = map hash votes ;
              leadershipProof = record { proof = emptyBS } ; -- FIXME
              payload = txs ;
              signature = record { bytes = emptyBS } -- FIXME
            }
      in SomeBlock newBlock , ⟨ p , (extendTree blockTree) tree newBlock ⟩
```
## Global state

```agda
    record Stateᵍ : Set where
      constructor ⟪_,_,_,_,_,_⟫
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
* The list of parties determines the execution order
```agda
        executionOrder : List PartyId
```
* Current voting round
```agda
        votingRound : RoundNumber
```
```agda
    open Stateᵍ public
```

# Network

Retrieving a messages from the global message buffer

```agda
    retrieve : PartyId → Stateᵍ → List Message × List Envelope
    retrieve p N =
        let msgs = filterᵇ (λ {⦅ m , r , d ⦆ → ⌊ p ≟ r ⌋ ∧ ⌊ d Fin.≟ zero ⌋ }) (messages N)
            rest = filterᵇ (λ {⦅ m , r , d ⦆ → not (⌊ p ≟ r ⌋ ∧ ⌊ d Fin.≟ zero ⌋) }) (messages N)
        in map (λ { ⦅ m , _ , _ ⦆ → m }) msgs , rest
      where open Relation.Binary.Bundles.DecSetoid (StrictTotalOrder.Eq.decSetoid PartyIdO)
```
Broadcasting messages, i.e. updating the global message buffer

```agda
    broadcast : Message → Stateᵍ → Stateᵍ
    broadcast m N =
      record N {
        messages = (map (λ { p → ⦅ m , p , suc zero ⦆ }) (executionOrder N)) ++ messages N ;
        history = m ∷ history N
      }
```
## Receive

A party receives messages from the global state by fetching messages assigned to the party,
updating the local block tree and putting the local state back into the global state.

```agda
    data _[_]⇀_ : {p : PartyId} → Stateᵍ → Honesty p → Stateᵍ → Set where

      honestNoState : ∀ {p N}
        → lookup (stateMap N) p ≡ nothing
          -------------------------------
        → N [ Honest {p} ]⇀ N

      honest : ∀ {p N} {s s′ : Stateˡ} {msg} {rest}
        → lookup (stateMap N) p ≡ just s
        → (msg , rest) ≡ retrieve p N
        → s′ ≡ honestReceive msg s
          ------------------------
        → N [ Honest {p} ]⇀
          record N {
              stateMap = M.insert p s′ (stateMap N) ;
              messages = rest
            }

      corrupt : ∀ {p N}
          ---------------------
        → N [ Corrupt {p} ]⇀ N
```

## Create

A party can create a new block by adding it to the local block tree and gossiping the
block creation messages to the other parties. The local state gets updated in the global
state.

```agda
    data _[_]↷_ : {p : PartyId} → Stateᵍ → Honesty p → Stateᵍ → Set where

      honestNoState : ∀ {p N}
        → lookup (stateMap N) p ≡ nothing
          -------------------------------
        → N [ Honest {p} ]↷ N

      honest : ∀ {p M N} {s s′ : Stateˡ} {msg}
        → lookup (stateMap M)  p ≡ just s
        → isSlotLeader p (clock M) ≡ true
        → (msg , s′) ≡ honestCreate (clock M) (votingRound M) (txSelection (clock M) p) s
        → N ≡ broadcast msg M
          ------------------------------------------------------------------
        → M [ Honest {p} ]↷
          record N {
              stateMap = M.insert p s′ (stateMap N)
            }

      corrupt : ∀ {p N}
          ---------------------
        → N [ Corrupt {p} ]↷ N
```

## Voting

### Comittee membership

```agda
    data CommitteeMember : PartyId → RoundNumber → Set where

    -- TODO: add constructor
```

An honest party votes as follows:

```agda
    honestVote : Slot → RoundNumber → Stateˡ → Message
    honestVote sl r ⟨ partyId , tree ⟩ =
      SomeVote record {
        votingRound = r ;
        creatorId = partyId ;
        committeeMembershipProof = record { proofM = emptyBS } ; -- FIXME
        blockHash = tip ((bestChain blockTree) sl tree) ; -- Currently just selecting the tip of the best chain to vote
        signature = record { bytes = emptyBS } -- FIXME
      }
```

A party can cast a vote for a block, if the party is a member of the voting committee

```agda
    data _[_]⇉_ : {p : PartyId} → Stateᵍ → Honesty p → Stateᵍ → Set where

      honest : ∀ {p M N} {s} {msg}
        → lookup (stateMap M)  p ≡ just s
        → CommitteeMember p (votingRound M)
        → msg ≡ honestVote (clock M) (votingRound M) s
        → N ≡ broadcast msg M
        → M [ Honest {p} ]⇉ N
```

# Small-step semantics

The small-step semantics describe the evolution of the global state.

```agda
    data _↝_ : Stateᵍ → Stateᵍ → Set where

      Deliver : ∀ {M N p} {h : Honesty p}
        → M [ h ]⇀ N
          ---------------------------
        → M ↝ N

      CastVote : ∀ {M N p} {h : Honesty p}
        → M [ h ]⇉ N
          ----------------------
        → M ↝ N

      Bake : ∀ {M N p} {h : Honesty p}
        → M [ h ]↷ N
          -----------------------
        → M ↝ N

      NextRound : ∀ {M}
          ------------------------------
        → M ↝ record M {
                 clock = suc (clock M)
               }

      PermParties : ∀ {N ps}
        → executionOrder N ↭ ps
          ---------------------------
        → N ↝ record N {
                 executionOrder = ps
               }

      PermMsgs : ∀ {N ms}
        → messages N ↭ ms
          --------------------
        → N ↝ record N {
                 messages = ms
               }
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

# Collision free predicate

```agda
    data CollisionFree (N : Stateᵍ) : Set where

      collision-free : ∀ {b₁ b₂ : Block}
        → All
          (λ { (m₁ , m₂) → m₁ ≡ SomeBlock b₁ → m₂ ≡ SomeBlock b₂ →
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

    -- Create

    -- TODO: implement Gossip data type
    postulate
      hist-honestGossipMsgs : ∀ {M N} {msg}
        → N ≡ broadcast msg M
        → history N ⊇ history M

    []↷-hist-common-prefix : ∀ {M N p} {h : Honesty p}
      → M [ h ]↷ N
      → history M ⊆ₘ history N
    []↷-hist-common-prefix (honestNoState _) x = x
    []↷-hist-common-prefix (honest {msg = msg} _ _ x x₁) = hist-honestGossipMsgs {msg = msg} x₁
    []↷-hist-common-prefix corrupt x = x

    []↷-collision-free : ∀ {M N p} {h : Honesty p}
      → CollisionFree N
      → M [ h ]↷ N
      → CollisionFree M
    []↷-collision-free cf-N M[]↷N = collision-free-resp-⊇ cf-N ([]↷-hist-common-prefix M[]↷N)

    postulate
      []⇉-collision-free : ∀ {M N p} {h : Honesty p}
        → CollisionFree N
        → M [ h ]⇉ N
        → CollisionFree M

    ∷-collision-free : ∀ {cl sm ms hs ps r p}
      → CollisionFree ⟪ cl , sm , ms , hs , p ∷ ps , r ⟫
      → CollisionFree ⟪ cl , sm , ms , hs , ps , r ⟫
    ∷-collision-free (collision-free {b₁} {b₂} cf) = collision-free {b₁ = b₁} {b₂ = b₂} cf
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
    ↝-collision-free (CastVote x) cf-N₂ = []⇉-collision-free cf-N₂ x
    ↝-collision-free (Bake x) cf-N₂ =  []↷-collision-free cf-N₂ x
    ↝-collision-free NextRound (collision-free x) = collision-free x
    ↝-collision-free (PermParties _) (collision-free x) = collision-free x
    ↝-collision-free (PermMsgs _) (collision-free x) = collision-free x
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
