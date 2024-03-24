```agda
module Peras.SmallStep where
```

<!--
```agda
open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.List as List using (List; all; foldr; _∷_; []; _++_; filter; filterᵇ; map; cartesianProduct; length; head; catMaybes)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Any using (Any; _─_; _∷=_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (suc; pred; _≤_; _<_; _≤ᵇ_; _≤?_; _<?_; _≥_; ℕ; _+_; _*_; _∸_; _≟_; _>_)
open import Data.Nat.Properties using (≤-totalOrder)
open import Data.Fin using (Fin; zero; suc) renaming (pred to decr)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
open import Function.Base using (_∘_; id; _$_; flip)
open import Relation.Binary.Bundles using (StrictTotalOrder)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym; subst; trans)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Data.List.Extrema (≤-totalOrder) using (argmax)

open import Peras.Chain
open import Peras.Crypto
open import Peras.Block
open import Peras.Params

open import Data.Tree.AVL.Map PartyIdO as M using (Map; lookup; insert; empty)
open import Data.List.Relation.Binary.Subset.Propositional {A = Block} using (_⊆_)

open Honesty public
open MembershipProof public
open Signature public
open RoundNumber public
open Party
```
-->

# Small-step semantics

The small-step semantics define the possible evolution of the global state of the system
under the Peras protocol modelling honest and adversary parties.

The goal is to show *safety* and *liveness* for the protocol.

Reference: Formalizing Nakamoto-Style Proof of Stake, Søren Eller Thomsen and Bas Spitters

Messages for sending and receiving blocks, certificates and votes
```agda
data Message : Set where
  BlockMsg : Block → Message
  VoteMsg : Vote → Message
  CertMsg : Certificate → Message
```
Messages can be delayed by an adversary. Delay is either 0, 1, 2

```agda
Delay = Fin 3
```
Messages are put into an envelope which is assigned to a given party and is defined with
a delay.

```agda
record Envelope : Set where
  constructor ⦅_,_,_⦆
  field
    partyId : PartyId
    message : Message
    delay : Delay
```
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
module _ {block₀ : Block} {cert₀ : Certificate}
         {IsCommitteeMember : PartyId → RoundNumber → MembershipProof → Set}
         {IsVoteSignature : Vote → Signature → Set}
         {IsSlotLeader : PartyId → Slot → LeadershipProof → Set}
         {IsBlockSignature : Block → Signature → Set}
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
```agda
  getCert : RoundNumber → List Certificate → Maybe Certificate
  getCert (MkRoundNumber r) = head ∘ filter ((_≟ r) ∘ votingRoundNumber)
```
```agda
  latestCert : List Certificate → Certificate
  latestCert = argmax votingRoundNumber cert₀
```

## BlockTree

```agda
  record IsTreeType {tT : Set}
                    (tree₀ : tT)
                    (extendTree : tT → Block → tT)
                    (allBlocks : tT → List Block)
                    (bestChain : Slot → tT → Chain)
                    (addVote : tT → Vote → tT)
                    (addCert : tT → Certificate → tT)
                    (votes : tT → Chain → List Vote)
                    (certs : tT → Chain → List Certificate)
         : Set₁ where

    allBlocksUpTo : Slot → tT → List Block
    allBlocksUpTo sl t = filter ((_≤? sl) ∘ slotNumber) (allBlocks t)

    field
```
Properties that must hold with respect to blocks and votes

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
        → ∥ c , certs t c ∥ ≤ ∥ b , certs t b ∥

      self-contained : ∀ (t : tT) (sl : Slot)
        → bestChain sl t ⊆ allBlocksUpTo sl t

      valid-votes : ∀ (t : tT) (c : Chain)
        → All (ValidVote {IsCommitteeMember} {IsVoteSignature}) (votes t c)

      unique-votes : ∀ (t : tT) (v : Vote) (c : Chain)
        → let vs = votes t c
          in
          v ∈ vs
        → vs ≡ votes (addVote t v) c

      no-equivocations : ∀ (t : tT) (v : Vote) (c : Chain)
        → let vs = votes t c
          in
          Any (v ∻_) vs
        → vs ≡ votes (addVote t v) c

      non-quorum : ∀ (t : tT) (r : RoundNumber)
        → let sl = T * (roundNumber r)
              b = bestChain sl t
          in
          length (votes t b) < τ
        → getCert r (certs t b) ≡ nothing

      quorum : ∀ (t : tT) (r : RoundNumber) (c : Certificate)
        → let sl = T * (roundNumber r)
              b = bestChain sl t
          in
          length (votes t b) ≥ τ
        → getCert r (certs t b) ≡ just c

```
The block tree type

```agda
  record TreeType (T : Set) : Set₁ where

    field
      tree₀ : T
      extendTree : T → Block → T
      allBlocks : T → List Block
      bestChain : Slot → T → Chain

      addVote : T → Vote → T
      addCert : T → Certificate → T

      votes : T → Chain → List Vote
      certs : T → Chain → List Certificate

      is-TreeType : IsTreeType
                      tree₀ extendTree allBlocks bestChain
                      addVote addCert votes certs

    tipBest : Slot → T → Block
    tipBest sl t = tip (valid is-TreeType t sl) where open IsTreeType

    latestCertOnChain : Slot → T → Certificate
    latestCertOnChain sl t =
      let b = bestChain sl t
      in latestCert (catMaybes $ map certificate b)

    latestCertSeen : Slot → T → Certificate
    latestCertSeen sl t =
      let b = bestChain sl t
      in latestCert (certs t b)

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
           {parties : List PartyId}
           where
```
The local state initialized with the block tree

```agda
    Stateˡ = LocalState blockTree
```
### State update

Updating the local state upon receiving a message

```agda
    data _[_]→_ : Stateˡ → Message → Stateˡ → Set where

      VoteReceived : ∀ {v t}
        → ⟪ t ⟫ [ VoteMsg v ]→
          ⟪ addVote blockTree t v ⟫

      CertReceived : ∀ {c t}
        → ⟪ t ⟫ [ CertMsg c ]→
          ⟪ addCert blockTree t c ⟫

      BlockReceived : ∀ {b t}
        → ⟪ t ⟫ [ BlockMsg b ]→
          ⟪ extendTree blockTree t b ⟫
```
In a cooldown period there is no voting.

```agda
    data VoteInRound : Stateˡ → Chain → List Certificate → RoundNumber → Set where

      Regular : ∀ {c cs r t}
        → let certₛ = latestCertSeen blockTree (r * T) t
              rₛ = votingRoundNumber certₛ
        in
          rₛ + 1 ≥ r
        → Reference certₛ c
        → VoteInRound ⟪ t ⟫ c cs (MkRoundNumber r)

      AfterCooldown : ∀ {chain cs r c t}
        → let certₛ = latestCertSeen blockTree (r * T) t
              rₛ = votingRoundNumber certₛ
        in
          c > 0
        → r ≥ R + rₛ
        → r ≡ (c * K) + rₛ
        → VoteInRound ⟪ t ⟫ chain cs (MkRoundNumber r)
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

```agda
    Delivered : Stateᵍ → Set
    Delivered = All (λ { ⦅ _ , _ , d ⦆ → d ≢ zero }) ∘ messages where open Stateᵍ
```


Updating global state
```agda
    updateᵍ : Message → Delay → PartyId → Stateˡ → Stateᵍ → Stateᵍ
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
        clock = suc (clock M) ;
        messages = map (λ { ⦅ p , m , d ⦆ → ⦅ p , m , decr d ⦆}) (messages M)
      }
      where open Stateᵍ
```
## Receive

A party receives messages from the global state by fetching messages assigned to the party,
updating the local block tree and putting the local state back into the global state.

```agda
    data _[_,_]⇀_ : {p : PartyId} → Stateᵍ → Honesty p → Message → Stateᵍ → Set where
```
An honest party consumes a message from the global message buffer and updates the
the local state
```agda
      honest : ∀ {p} {lₚ lₚ′} {m} {c s ms hs as}
        → lookup s p ≡ just lₚ
        → (m∈ms : ⦅ p , m , zero ⦆ ∈ ms)
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
```
An adversarial party might delay a message
```agda
      corrupt : ∀ {p c s ms hs as as′} {m}
        → (m∈ms : ⦅ p , m , zero ⦆ ∈ ms)
          --------------------------------
        → ⟦ c
          , s
          , ms
          , hs
          , as
          ⟧ [ Corrupt {p} , m ]⇀
          ⟦ c
          , s -- TODO: insert p lₚ s
          , m∈ms ∷= ⦅ p , m , suc zero ⦆
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

      honest : ∀ {p} {t} {M} {prf} {sig}
        → let open Stateᵍ M
              r = v-round clock
              c = bestChain blockTree clock t
              cs = certs blockTree t c
              v = record {
                    votingRound = r ;
                    creatorId = p ;
                    committeeMembershipProof = prf ;
                    blockHash = hash (tipBest blockTree (clock ∸ L) t) ;
                    signature = sig                  }
          in
          lookup stateMap p ≡ just ⟪ t ⟫
        → IsVoteSignature v sig
        → StartOfRound clock r
        → IsCommitteeMember p r prf
        → VoteInRound ⟪ t ⟫ c cs r
          ---------------------------------------------------
        → M [ Honest {p} ]⇉
          updateᵍ (VoteMsg v) (suc zero) p ⟪ addVote blockTree t v ⟫ M
```
Rather than creating a delayed vote, an adversary can honestly create it and delay the message

## Create

A party can create a new block by adding it to the local block tree and gossiping the
block creation messages to the other parties. The local state gets updated in the global
state.

```agda
    data _[_]↷_ : {p : PartyId} → Stateᵍ → Honesty p → Stateᵍ → Set where

      honest : ∀ {p} {t} {M} {prf} {sig}
        → let open Stateᵍ M
              r = roundNumber (v-round clock)
              txs = txSelection clock p
              c = bestChain blockTree (pred clock) t
              cs = certs blockTree t c
              body = record {
                  blockHash = hash txs ;
                  payload = txs
                  }
              b = record {
                    slotNumber = clock ;
                    creatorId = p ;
                    parentBlock = hash (tipBest blockTree (pred clock) t) ;
                    certificate = just (latestCertSeen blockTree (pred clock) t) ;
                    leadershipProof = prf ;
                    bodyHash = blockHash body ;
                    signature = sig
                  }
          in
          lookup stateMap p ≡ just ⟪ t ⟫
        → IsBlockSignature b sig
        → getCert (MkRoundNumber (r ∸ 2)) cs ≡ nothing

        → IsSlotLeader p clock prf
          -------------------------------------------
        → M [ Honest {p} ]↷ updateᵍ (BlockMsg b) (suc zero) p
             ⟪ extendTree blockTree t b ⟫ M
```
Rather than creating a delayed block, an adversary can honestly create it and delay the message

# Small-step semantics

The small-step semantics describe the evolution of the global state.

```agda
    data _↝_ : Stateᵍ → Stateᵍ → Set where

      Deliver : ∀ {M N p} {h : Honesty p} {m}
        → M [ h , m ]⇀ N
          ---------------
        → M ↝ N

      CastVote : ∀ {M N p} {h : Honesty p}
        → Delivered M
        → M [ h ]⇉ N
          -----------
        → M ↝ N

      -- TODO: Create Cert

      CreateBlock : ∀ {M N p} {h : Honesty p}
        → Delivered M
        → M [ h ]↷ N
          -----------
        → M ↝ N

      NextSlot : ∀ {M}
        → Delivered M
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
Post-composition
```agda
    ↝∘↝⋆ : ∀ {M N O}
      → M ↝⋆ N
      → N ↝ O
      → M ↝⋆ O
    ↝∘↝⋆ {M} {N} {O} (_ ∎) N↝O = M ↝⟨ N↝O ⟩ (O ∎)
    ↝∘↝⋆ {M} (_ ↝⟨ M↝M₁ ⟩ M₁↝⋆N) N↝O = M ↝⟨ M↝M₁ ⟩ (↝∘↝⋆ M₁↝⋆N N↝O)
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
    []↷-hist-common-prefix (honest {p} {t} {M} {prf} {sig} _ _ _ _) =
      let r = roundNumber (v-round (clock M))
          txs = txSelection (clock M) p
          body = record {
              blockHash = hash txs ;
              payload = txs
              }
          b = record {
                slotNumber = clock M ;
                creatorId = p ;
                parentBlock = hash (tipBest blockTree (pred (clock M)) t) ;
                certificate = just (latestCertSeen blockTree (pred (clock M)) t) ;
                leadershipProof = prf ;
                bodyHash = blockHash body ;
                signature = sig
              }
       in xs⊆x∷xs (history M) (BlockMsg b)

    []⇉-hist-common-prefix : ∀ {M N p} {h : Honesty p}
      → M [ h ]⇉ N
      → history M ⊆ₘ history N
    []⇉-hist-common-prefix {M} (honest {p} {t} {M} {prf} {sig} _ _ _ _ _) =
      let r = v-round (clock M)
          v = record {
                votingRound = r ;
                creatorId = p ;
                committeeMembershipProof = prf ;
                blockHash = hash (tipBest blockTree ((clock M) ∸ L) t) ;
                signature = sig
              }
      in xs⊆x∷xs (history M) (VoteMsg v)

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
    ↝-collision-free (CastVote _ x) cf-N₂ = []⇉-collision-free cf-N₂ x
    ↝-collision-free (CreateBlock _ x) cf-N₂ =  []↷-collision-free cf-N₂ x
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
        → M [ Corrupt {p} ]↷ N
        → All (λ { m → (m ≡ BlockMsg b × HonestBlock b)
            → m ∈ history M }) (history N)
        → ForgingFree N
```
