```agda
module Peras.SmallStep where
```

<!--
```agda
open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.List as List using (List; all; foldr; _∷_; []; _++_; filter; filterᵇ; map; cartesianProduct; length; head)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Any using (Any; _─_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (suc; pred; _≤_; _<_; _≤ᵇ_; _≤?_; _<?_; _≥_; ℕ; _+_; _*_; _∸_; _≟_)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
open import Function.Base using (_∘_; id; _$_)
open import Relation.Binary.Bundles using (StrictTotalOrder)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; subst; trans)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Peras.Chain -- using (Chain; tip; Vote; RoundNumber; ValidChain; VoteInRound; ∥_∥; ⟨_,_,_⟩; Dangling; v-round; DanglingVotes; _∻_)
open import Peras.Crypto using (Hashable; emptyBS; MembershipProof; Signature; Hash)

open import Peras.Block
open import Peras.Params

open import Data.Tree.AVL.Map PartyIdO as M using (Map; lookup; insert; empty)
open import Data.List.Relation.Binary.Subset.Propositional {A = Block} using (_⊆_)

open Chain public
open Honesty public
open MembershipProof public
open Signature public
open RoundNumber public
-- open Vote
open Party
```
-->

# Small-step semantics

The small-step semantics define the possible evolution of the global state of the system
under the Peras protocol modelling honest and adversary parties.

The goal is to show *safety* and *liveness* for the protocol.

Reference: Formalizing Nakamoto-Style Proof of Stake, Søren Eller Thomsen and Bas Spitters

Messages for sending and receiving blocks, votes and chains
```agda
data Message : Set where
  BlockMsg : Block → Message
  VoteMsg : Vote → Message
  CertMsg : Certificate → Message
  ChainMsg : Chain → Message
```
Messages are put into an envelope
```agda
record Envelope : Set where
  constructor ⦅_,_,_⦆
  field
    partyId : PartyId
    message : Message
    delay : ℕ
```
<!--
```agda
-- We introduce the relation ≐ to denote that two lists have the same elements
open import Relation.Binary.Core using (Rel)
_≐_ : Rel (List Block) _
P ≐ Q = (P ⊆ Q) × (Q ⊆ P)
```
-->

block₀ denotes the genesis block that is passed in as a module parameter

```agda
module _ {block₀ : Block}
         ⦃ _ : Hashable Block ⦄
         ⦃ _ : Hashable (List Tx) ⦄
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
                    (newChain : T → Chain → T)
                    (allBlocks : T → List Block)
                    (bestChain : Slot → T → Chain)
                    (addVote : T → Vote → T)
                    (addCert : T → Certificate → T)
                    (votes : T → Chain → List Vote)
                    (certs : T → Chain → List Certificate)
         : Set₁ where

    allBlocksUpTo : Slot → T → List Block
    allBlocksUpTo sl t = filter ((_≤? sl) ∘ slotNumber) (allBlocks t)

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
        → let b = bestChain sl t
          in
          ValidChain {block₀} c
        → blocks c ⊆ allBlocksUpTo sl t
        → ∥ c , certs t c ∥ ≤ ∥ b , certs t b ∥

      self-contained : ∀ (t : T) (sl : Slot)
        → blocks (bestChain sl t) ⊆ allBlocksUpTo sl t
```
The block tree type

```agda
  record TreeType (T : Set) : Set₁ where

    field
      tree₀ : T
      extendTree : T → Block → T
      newChain : T → Chain → T
      allBlocks : T → List Block
      bestChain : Slot → T → Chain

      addVote : T → Vote → T
      addCert : T → Certificate → T

      votes : T → Chain → List Vote
      certs : T → Chain → List Certificate

      is-TreeType : IsTreeType
                      tree₀ extendTree newChain allBlocks bestChain
                      addVote addCert votes certs

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
# Parameterized module

  * blockTree
  * slot leader computable predicate
  * voting committee membership predicate
  * tx selection
  * The list of parties
  * AdversarialState₀ is the initial adversarial state


```agda
  module _ {tT : Set}
           {blockTree : TreeType tT}
           {AdversarialState : Set}
           {adversarialsState₀ : AdversarialState}
           {IsSlotLeader : PartyId → Slot → Set}
           {IsCommitteeMember : PartyId → RoundNumber → Set}
           {txSelection : Slot → PartyId → List Tx}
           {parties : List PartyId}
           {createCertificate : Vote → Certificate}
           where
```
The local state initialized with the block tree

```agda
    Stateˡ = LocalState blockTree
```
```agda
    getCert : RoundNumber → List Certificate → Maybe Certificate
    getCert (MkRoundNumber r) = head ∘ filter ((_≟ r) ∘ Certificate.roundNumber)
```
### State update

Updating the local state upon receiving a message

```agda
    data _[_]→_ : Stateˡ → Message → Stateˡ → Set where
```
A new vote is added as dangling vote to the local state, when
  * the vote has not already been seen (on-chain or dangling)
  * the vote is not an equivocation (on-chain or dangling)

```agda
      VoteReceived : ∀ {v t}
        → let r = votingRound v
              s = T * (roundNumber r)
              b = (bestChain blockTree) s t
              vs = (votes blockTree) t b
              cs = (certs blockTree) t b
              t′ = (addVote blockTree) t v
              b′ = (bestChain blockTree) s t′
              vs′ = (votes blockTree) t′ b′
          in
          v ∉ vs
        → getCert r cs ≡ nothing
        → ¬ (Any (v ∻_) vs)
        → length vs′ < τ
        → ⟪ t ⟫ [ VoteMsg v ]→ ⟪ t′ ⟫
```
```agda
      VoteReceivedNewCert : ∀ {v t}
        → let r = votingRound v
              s = T * (roundNumber r)
              b = (bestChain blockTree) s t
              vs = (votes blockTree) t b
              cs = (certs blockTree) t b
              t′ = (addVote blockTree) t v
              b′ = (bestChain blockTree) s t′
              vs′ = (votes blockTree) t′ b′
          in
          v ∉ vs
        → getCert r cs ≡ nothing
        → ¬ (Any (v ∻_) vs)
        → length vs′ ≥ τ
        → ⟪ t ⟫ [ VoteMsg v ]→ ⟪ (addCert blockTree) t′ (createCertificate v) ⟫
```
```agda
      CertReceived : ∀ {c t}
        → let r = Certificate.roundNumber c
              s = T * r
              b = (bestChain blockTree) s t
              cs = (certs blockTree) t b
          in
          getCert (MkRoundNumber (Certificate.roundNumber c)) cs ≡ nothing
        → ⟪ t ⟫ [ CertMsg c ]→ ⟪ (addCert blockTree) t c ⟫
```

When a chain is received it is added the the blockTree only if it
is heavier than the current best chain with respect of the dangling
votes.

```agda
      ChainReceived : ∀ {c t}
        → let b = (bestChain blockTree) (slotNumber (tip c)) t
          in
            ∥ b , (certs blockTree) t b ∥ < ∥ c , (certs blockTree) t c ∥
          → ⟪ t ⟫ [ ChainMsg c ]→ ⟪ (newChain blockTree) t c ⟫
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
Updating global state
```agda
    updateᵍ : Message → ℕ → PartyId → Stateˡ → Stateᵍ → Stateᵍ
    updateᵍ m d p l ⟦ c , s , ms , hs , as ⟧ =
          ⟦ c
          , insert p l s
          , map ⦅_, m , d ⦆ parties ++ ms
          , m ∷ hs
          , as
          ⟧
```
Ticking the global clock
```agda
    tick : Stateᵍ → Stateᵍ
    tick M =
      record M {
        clock = suc (clock M)
      }
      where open Stateᵍ
```
Delaying messages
```agda
    data Delay : Envelope → Envelope → Set where

      Id : ∀ {e : Envelope} →
        Delay e e

      Delayed : ∀ {d m p} →
        Delay ⦅ d , m , p ⦆ ⦅ suc d , m , p ⦆

    data δ : List Envelope → List Envelope → Set where

      Empty : δ [] []

      Cons : ∀ {e e′} {es es′}
        → Delay e e′
        → δ es es′
        → δ (e ∷ es) (e′ ∷ es′)
```

## Receive

A party receives messages from the global state by fetching messages assigned to the party,
updating the local block tree and putting the local state back into the global state.

```agda
    data _[_,_]⇀_ : {p : PartyId} → Stateᵍ → Honesty p → Message → Stateᵍ → Set where

      honest : ∀ {p} {lₚ lₚ′} {m} {c s ms hs as}
        → lookup s p ≡ just lₚ
        → (m∈ms : ⦅ 0 , m , p ⦆ ∈ ms)
        → lₚ [ m ]→ lₚ′
          ------------------------
        → ⟦ c
          , s
          , ms
          , hs
          , as
          ⟧ [ Honest {p} , m ]⇀
          ⟦ c
          , insert p lₚ′ s
          , ms ─ m∈ms
          , hs
          , as
          ⟧

      corrupt : ∀ {p c s ms ms′ hs as as′} {lₚ} {m}
        → δ ms ms′
          ------------------------------------
        → ⟦ c
          , s
          , ms
          , hs
          , as
          ⟧ [ Corrupt {p} , m ]⇀
          ⟦ c
          , insert p lₚ s
          , ms′
          , hs
          , as′
          ⟧
```
## Vote

A party can cast a vote for a block, if
  * the current slot is the first slot in a voting round
  * the party is a member of the voting committee
  * the chain is not in a cooldown phase

```agda
    data _[_]⇉_ : {p : PartyId} → Stateᵍ → Honesty p → Stateᵍ → Set where

      honest : ∀ {p} {t} {M}
        → let open Stateᵍ M
              r = v-round clock
              c = (bestChain blockTree) clock t
              cs = (certs blockTree) t c
              b = (bestChain blockTree) (clock ∸ L) t
              v = record {
                    votingRound = r ;
                    creatorId = p ;
                    committeeMembershipProof =
                      record { proofM = emptyBS } ; -- FIXME
                    blockHash = hash (tip b) ;
                    signature =
                      record { bytes = emptyBS }  -- FIXME
                  }
          in
          lookup stateMap p ≡ just ⟪ t ⟫

        → StartOfRound clock r
        → IsCommitteeMember p r
        → VoteInRound c cs r
          -----------------------------------------------------
        → M [ Honest {p} ]⇉
          updateᵍ (VoteMsg v) 0 p ⟪ (addVote blockTree) t v ⟫ M

      corrupt : ∀ {p c s ms ms′ hs as as′} {lₚ}
        → δ ms ms′
          --------------------------------
        → ⟦ c
          , s
          , ms
          , hs
          , as
          ⟧ [ Corrupt {p} ]⇉
          ⟦ c
          , insert p lₚ s
          , ms′
          , hs
          , as′
          ⟧
```
## Create

A party can create a new block by adding it to the local block tree and gossiping the
block creation messages to the other parties. The local state gets updated in the global
state.

```agda
    data _[_]↷_ : {p : PartyId} → Stateᵍ → Honesty p → Stateᵍ → Set where

      honest : ∀ {p} {t} {M}
        → let open Stateᵍ M
              r = roundNumber (v-round clock)
              txs = txSelection clock p
              c = (bestChain blockTree) (pred clock) t
              cs = (certs blockTree) t c
              body = record {
                  blockHash = hash txs ;
                  payload = txs
                  }
              b = record {
                    slotNumber = clock ;
                    creatorId = p ;
                    parentBlock = hash (tip c) ;
                    certificate = nothing ;
                    leadershipProof = record { proof = emptyBS } ; -- FIXME
                    bodyHash = blockHash body ;
                    signature = record { bytes = emptyBS } -- FIXME
                  }
          in
          lookup stateMap p ≡ just ⟪ t ⟫
        → getCert (MkRoundNumber (r ∸ 2)) cs ≡ nothing

        → IsSlotLeader p clock
          -------------------------------------------
        → M [ Honest {p} ]↷ updateᵍ (BlockMsg b) 0 p
             ⟪ (extendTree blockTree) t b ⟫ M

      corrupt : ∀ {p c s ms ms′ hs as as′} {lₚ}
        → δ ms ms′
          --------------------------------
        → ⟦ c
          , s
          , ms
          , hs
          , as
          ⟧ [ Corrupt {p} ]↷
          ⟦ c
          , insert p lₚ s
          , ms′
          , hs
          , as′
          ⟧
```

# Small-step semantics

The small-step semantics describe the evolution of the global state.

```agda
    data _↝_ : Stateᵍ → Stateᵍ → Set where

      Deliver : ∀ {M N p} {h : Honesty p} {m}
        → M [ h , m ]⇀ N
          ---------------
        → M ↝ N

      CastVote : ∀ {M N p} {h : Honesty p}
        → M [ h ]⇉ N
          -----------
        → M ↝ N

      CreateBlock : ∀ {M N p} {h : Honesty p}
        → M [ h ]↷ N
          -----------
        → M ↝ N

      NextSlot : ∀ {M}
          ------------
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
      → M [ h , m ]⇀ N
      → history M ⊆ₘ history N
    []-hist-common-prefix (honest _ _ _) x = x
    []-hist-common-prefix (corrupt _) x = x

    []⇀-collision-free : ∀ {M N p} {h : Honesty p} {m}
      → CollisionFree N
      → M [ h , m ]⇀ N
      → CollisionFree M
    []⇀-collision-free (collision-free {b₁} {b₂} x) (honest _ _ _) = collision-free {b₁ = b₁} {b₂ = b₂} x
    []⇀-collision-free (collision-free {b₁} {b₂} x) (corrupt _) = collision-free {b₁ = b₁} {b₂ = b₂} x

    -- Create

    []↷-hist-common-prefix : ∀ {M N p} {h : Honesty p}
      → M [ h ]↷ N
      → history M ⊆ₘ history N
    []↷-hist-common-prefix (honest {p} {t} {M} _ _ _) =
      let r = roundNumber (v-round (clock M))
          txs = txSelection (clock M) p
          c = (bestChain blockTree) (pred (clock M)) t
          body = record {
              blockHash = hash txs ;
              payload = txs
              }
          b = record {
                slotNumber = clock M ;
                creatorId = p ;
                parentBlock = hash (tip c) ;
                certificate = nothing ;
                leadershipProof = record { proof = emptyBS } ;
                bodyHash = blockHash body ;
                signature = record { bytes = emptyBS }
              }
       in xs⊆x∷xs (history M) (BlockMsg b)
    []↷-hist-common-prefix (corrupt _) x₁ = x₁

    []⇉-hist-common-prefix : ∀ {M N p} {h : Honesty p}
      → M [ h ]⇉ N
      → history M ⊆ₘ history N
    []⇉-hist-common-prefix {M} (honest {p} {t} {M} _ _ _ _) =
      let r = v-round (clock M)
          b = (bestChain blockTree) ((clock M) ∸ L) t
          v = record {
                votingRound = r ;
                creatorId = p ;
                committeeMembershipProof =
                  record { proofM = emptyBS } ;
                blockHash = hash (tip b) ;
                signature =
                  record { bytes = emptyBS }
              }
      in xs⊆x∷xs (history M) (VoteMsg v)
    []⇉-hist-common-prefix (corrupt _) x₁ = x₁

    []↷-collision-free : ∀ {M N p} {h : Honesty p}
      → CollisionFree N
      → M [ h ]↷ N
      → CollisionFree M
    []↷-collision-free cf-N M[]↷N = collision-free-resp-⊇ cf-N ([]↷-hist-common-prefix M[]↷N)

    []⇉-collision-free : ∀ {M N p} {h : Honesty p}
      → CollisionFree N
      → M [ h ]⇉ N
      → CollisionFree M
    []⇉-collision-free cf-N M[]⇉N = collision-free-resp-⊇ cf-N ([]⇉-hist-common-prefix M[]⇉N)
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
    ↝-collision-free (CreateBlock x) cf-N₂ =  []↷-collision-free cf-N₂ x
    ↝-collision-free NextSlot (collision-free x) = collision-free x
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
        → M [ Corrupt {p} ]↷ N
        → All (λ { m → (m ≡ BlockMsg b × HonestBlock b)
            → m ∈ history M }) (history N)
        → ForgingFree N
```
