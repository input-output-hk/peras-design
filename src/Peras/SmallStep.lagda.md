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
open import Data.Fin using (Fin; zero; suc) renaming (pred to decr)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂; curry; uncurry)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)

open import Function using (_∘_; id; _$_; flip)
open import Relation.Binary.Bundles using (StrictTotalOrder)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym; subst; trans)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; ¬?)
open import Relation.Nullary.Negation using (contradiction; contraposition)

open import Peras.Block
open import Peras.Chain
open import Peras.Crypto
open import Peras.Numbering
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

The small-step semantics of the **Peras** protocol define the evolution of the
global state of the system modelling *honest* and *adversarial* parties. The
number of parties is fixed during the execution of the protocol. In addition the
model is parameterized by the lotteries (for slot leadership and voting
committee membership) as well as the type of the block tree. Furthermore
adversarial parties share adversarial state, which is generic state.

The following sub-sections cover the Peras protocol (see Figure 2: The Peras
protocol)

  * [Fetching](SmallStep.lagda.md#fetching)
  * [Block creation](SmallStep.lagda.md#block-creation)
  * [Voting](SmallStep.lagda.md#voting)

References:
* Adaptively Secure Fast Settlement Supporting Dynamic Participation and Self-Healing
* Formalizing Nakamoto-Style Proof of Stake, Søren Eller Thomsen and Bas Spitters

#### Messages

Messages for sending and receiving blocks and votes. In the `Peras` protocol
certificates are not diffused explicitly with the exception of bootstraping the
system.
```agda
data Message : Set where
  BlockMsg : Block → Message
  VoteMsg : Vote → Message
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
Messages can be delayed by an adversary. Delay is either
  * *0* for not delayed
  * *1* when delayed to the next slot.

TODO: Rethink network delay model
```agda
Delay = Fin 2
```
Messages are put into an envelope and assigned to a party. The message can be
delayed.
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

### Parameters

The model takes a couple of parameters: `block₀` denotes the genesis block,
`cert₀` is certificate for the first voting round referencing the genesis block.
In addition there are the following relations abstracting the lotteries (slot
leadership and voting committee membership) and the cryptographic signatures

  * `IsCommitteeMember`
  * `IsVoteSignature`
  * `IsSlotLeader`
  * `IsBlockSignature`

The parameters for the Peras protocol and hash functions are defined as instance
arguments of the module.
```agda
module _ {block₀ : Block} {cert₀ : Certificate}
         {IsCommitteeMember : PartyId → RoundNumber → MembershipProof → Set}
         {IsVoteSignature : Vote → Signature → Set}
         {IsSlotLeader : PartyId → SlotNumber → LeadershipProof → Set}
         {IsBlockSignature : Block → Signature → Set}
         ⦃ _ : Hashable Block ⦄
         ⦃ _ : Hashable (List Tx) ⦄
         ⦃ _ : Params ⦄
         where
```
  The block tree, resp. the validity of the chain is defined with respect of the
  parameters.
```agda
  open Hashable ⦃...⦄
  open Params ⦃...⦄
```
#### Block-tree

A block-tree is defined by properties - an implementation of the block-tree
has to fulfil all the properties mentioned below:

```agda
  record IsTreeType {T : Set}
                    (tree₀ : T)
                    (extendTree : T → Block → T)
                    (allBlocks : T → List Block)
                    (bestChain : SlotNumber → T → Chain)
                    (addVote : T → Vote → T)
                    (votes : T → List Vote)
                    (certs : T → List Certificate)
         : Set₁ where

    allBlocksUpTo : SlotNumber → T → List Block
    allBlocksUpTo sl t = filter ((_≤? getSlotNumber sl) ∘ slotNumber') (allBlocks t)

    field
```
Properties that must hold with respect to blocks and votes.

TODO: Use the properties (A1) - (A9) of the block-tree with certificates instead
as proposed in the paper.

```agda
      instantiated :
        allBlocks tree₀ ≡ block₀ ∷ []

      instantiated-certs :
        certs tree₀ ≡ cert₀ ∷ []

      extendable : ∀ (t : T) (b : Block)
        → allBlocks (extendTree t b) ≐ (b ∷ allBlocks t)

      extendable-certs : ∀ (t : T) (b : Block)
        → certs (extendTree t b) ≡ certs t

      extendable-votes : ∀ (t : T) (v : Vote)
        → allBlocks (addVote t v) ≐ allBlocks t

      valid : ∀ (t : T) (sl : SlotNumber)
        → ValidChain {block₀} {IsSlotLeader} {IsBlockSignature} (bestChain sl t)

      optimal : ∀ (c : Chain) (t : T) (sl : SlotNumber)
        → let b = bestChain sl t
              cts = certs t
          in
          ValidChain {block₀} {IsSlotLeader} {IsBlockSignature} c
        → c ⊆ allBlocksUpTo sl t
        → ∥ c ∥ cts ≤ ∥ b ∥ cts

      self-contained : ∀ (t : T) (sl : SlotNumber)
        → bestChain sl t ⊆ allBlocksUpTo sl t

      valid-votes : ∀ (t : T)
        → All (ValidVote {IsCommitteeMember} {IsVoteSignature}) (votes t)

      unique-votes : ∀ (t : T) (v : Vote)
        → let vs = votes t
          in
          v ∈ vs
        → vs ≡ votes (addVote t v)

      no-equivocations : ∀ (t : T) (v : Vote)
        → let vs = votes t
          in
          Any (v ∻_) vs
        → vs ≡ votes (addVote t v)

      non-quorum : ∀ (t : T) (r : RoundNumber)
        → length (votes t) < τ
        → findCert r (certs t) ≡ nothing

      quorum : ∀ (t : T) (r : RoundNumber) (c : Certificate)
        → length (votes t) ≥ τ
        → findCert r (certs t) ≡ just c

```
In addition to blocks the block-tree manages votes and certificates as well.
The block tree type is defined as follows:
```agda
  record TreeType (T : Set) : Set₁ where

    field
      tree₀ : T
      extendTree : T → Block → T
      allBlocks : T → List Block
      bestChain : SlotNumber → T → Chain

      addVote : T → Vote → T

      votes : T → List Vote
      certs : T → List Certificate

      is-TreeType : IsTreeType
                      tree₀ extendTree allBlocks bestChain
                      addVote votes certs

    tipBest : SlotNumber → T → Block
    tipBest sl t = tip (valid is-TreeType t sl) where open IsTreeType

    latestCertOnChain : SlotNumber → T → Certificate
    latestCertOnChain s = latestCert cert₀ ∘ catMaybes ∘ map certificate ∘ bestChain s

    latestCertSeen : T → Certificate
    latestCertSeen = latestCert cert₀ ∘ certs
```
### Additional parameters

In addition to the parameters already introduced above we introduce the
following parameters

  * The type of the block-tree
  * adversarialState₀ is the initial adversarial state
  * Tx selection function per party and slot number
  * The list of parties

```agda
  module _ {T : Set} {blockTree : TreeType T}
           {S : Set} {adversarialState₀ : S}
           {txSelection : SlotNumber → PartyId → List Tx}
           {parties : Parties}

           where

    open TreeType blockTree
```
#### Block-tree update

Updating the block-tree upon receiving a message for vote and block messages.

```agda
    data _[_]→_ : T → Message → T → Set where

      VoteReceived : ∀ {v t}
          ----------------------------
        → t [ VoteMsg v ]→ addVote t v

      BlockReceived : ∀ {b t}
          --------------------------------
        → t [ BlockMsg b ]→ extendTree t b
```
#### Vote in round

When does a party vote in a round? The protocol expects regular voting, i.e. if
in the previous round a quorum has been achieved or that voting resumes after a
cool-down phase.
```agda
    data VoteInRound : T → RoundNumber → Set where

      Regular : ∀ {r t} →
        let
          pref = bestChain (MkSlotNumber $ r * U) t
          cert′ = latestCertSeen t
        in
          r ≡ (roundNumber cert′) + 1 -- VR-1A
        → cert′ PointsInto pref       -- VR-1B
          -------------------------------
        → VoteInRound t (MkRoundNumber r)

      AfterCooldown : ∀ {r c t} →
        let
          cert⋆ = latestCertOnChain (MkSlotNumber $ r * U) t
          cert′ = latestCertSeen t
        in
          c > 0
        → r ≥ (roundNumber cert′) + R       -- VR-2A
        → r ≡ (roundNumber cert⋆) + (c * K) -- VR-2B
          ---------------------------------
        → VoteInRound t (MkRoundNumber r)
```
### State

The small-step semantics rely on a global state.

```agda
    record State : Set where
      constructor ⟦_,_,_,_,_⟧
      field
```
The global state consists of the following fields:

* Current slot of the system
```agda
        clock : SlotNumber
```
* Map with local state per party
```agda
        stateMap : Map T
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
        adversarialState : S
```
Progress
```agda
    Delivered : State → Set
    Delivered = All (λ { z → delay z ≢ zero }) ∘ messages where open State
```
Updating global state
```agda
    _,_,_,_↑_ : Message → Delay → PartyId → T → State → State
    m , d , p , l ↑ ⟦ c , s , ms , hs , as ⟧ =
      ⟦ c , insert p l s , map (uncurry ⦅_,_, m , d ⦆) (filter (¬? ∘ (p ≟_) ∘ proj₁) parties) ++ ms , m ∷ hs , as ⟧
```
Ticking the global clock
```agda
    tick : State → State
    tick M =
      record M {
        clock = next (clock M) ;
        messages = map (λ where
          e → record e { delay = decr (delay e) }) (messages M)
      }
      where open State
```
## Fetching

A party receives messages from the global state by fetching messages assigned to
the party, updating the local block tree and putting the local state back into
the global state.

```agda
    data _⊢_[_]⇀_ : {p : PartyId} → Honesty p → State → Message → State → Set where
```
An honest party consumes a message from the global message buffer and updates
the local state
```agda
      honest : ∀ {p} {t t′} {m} {c s ms hs as}
        → lookup s p ≡ just t
        → (m∈ms : ⦅ p , Honest , m , zero ⦆ ∈ ms)
        → t [ m ]→ t′
          ----------------------------------------
        → Honest {p} ⊢
          ⟦ c
          , s
          , ms
          , hs
          , as
          ⟧ [ m ]⇀
          ⟦ c
          , insert p t′ s
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
          , s -- TODO: insert p t s
          , m∈ms ∷= ⦅ p , Corrupt , m , suc zero ⦆
          , hs
          , as′
          ⟧
```
## Voting

A party can cast a vote for a block, if
  * the current slot is the first slot in a voting round
  * the party is a member of the voting committee
  * the chain is not in a cool-down phase

Voting updates the party's local state and for all other parties a message
is added to be consumed immediately.
```agda
    data _⊢_⇉_ : {p : PartyId} → Honesty p → State → State → Set where

      honest : ∀ {p} {t} {M} {prf} {sig} {vote}
        → let open State M
              r = v-round clock
              v = record
                    { votingRound = r
                    ; creatorId = p
                    ; proofM = prf
                    ; blockHash = hash $ tipBest (clock earlierBy L) t
                    ; signature = sig
                    }
          in
          vote ≡ v
        → lookup stateMap p ≡ just t
        → IsVoteSignature v sig
        → StartOfRound clock r
        → IsCommitteeMember p r prf
        → VoteInRound t r
          ----------------------------------------------
        → Honest {p} ⊢
            M ⇉ (VoteMsg v , zero , p , addVote t v ↑ M)
```
Rather than creating a delayed vote, an adversary can honestly create it and
delay the message.

## Block creation

A party can create a new block by adding it to the local block tree and
gossiping the block creation messages to the other parties. Block creation is
possible, if
  * the block signature is correct
  * the party is the slot leader

Block creation updates the party's local state and for all other parties a
message is added to be consumed immediately.
```agda
    data _⊢_↷_ : {p : PartyId} → Honesty p → State → State → Set where
```
During regular execution of the protocol, i.e. not in cool-down phase, no
certificate reference is included in the block.
```agda
      honest : ∀ {p} {t} {M} {prf} {sig} {block}
        → let open State M
              txs = txSelection clock p
              b = record
                    { slotNumber = clock
                    ; creatorId = p
                    ; parentBlock = hash $ tipBest clock t
                    ; certificate = nothing
                    ; leadershipProof = prf
                    ; bodyHash = blockHash
                        record { blockHash = hash txs
                               ; payload = txs
                               }
                    ; signature = sig
                    }
          in
          block ≡ b
        → lookup stateMap p ≡ just t
        → IsBlockSignature b sig
        → IsSlotLeader p clock prf
          --------------------------------------------------
        → Honest {p} ⊢
            M ↷ (BlockMsg b , zero , p , extendTree t b ↑ M)
```
During a cool-down phase, the block includes a certificate reference.
```agda
      honest-cooldown : ∀ {p} {t} {M} {prf} {sig} {block}
        → let open State M
              r = getRoundNumber (v-round clock)
              txs = txSelection clock p
              b = record
                    { slotNumber = clock
                    ; creatorId = p
                    ; parentBlock = hash $ tipBest clock t
                    ; certificate = nothing -- TODO: add certificate
                    ; leadershipProof = prf
                    ; bodyHash = blockHash
                        record { blockHash = hash txs
                               ; payload = txs
                               }
                    ; signature = sig
                    }
              cert⋆ = latestCertOnChain (MkSlotNumber $ r * U) t
              cert′ = latestCertSeen t
              cts = certs t
          in
          block ≡ b
        → lookup stateMap p ≡ just t
        → IsBlockSignature b sig
        → IsSlotLeader p clock prf
        → ¬ Any (λ { c → (roundNumber c) + 2 ≡ r }) cts -- (a)
        → r ≤ A + (roundNumber cert′)                   -- (b)
        → (roundNumber cert′) > (roundNumber cert⋆)     -- (c)
          ----------------------------------------------------
        → Honest {p} ⊢
            M ↷ (BlockMsg b , zero , p , extendTree t b ↑ M)
```
Rather than creating a delayed block, an adversary can honestly create it and
delay the message.

## Small-step semantics

The small-step semantics describe the evolution of the global state.

```agda
    variable
      M N O : State
      p : PartyId
      h : Honesty p
```
```agda
    data _↝_ : State → State → Set where

      Deliver : ∀ {m}
        → h ⊢ M [ m ]⇀ N
          --------------
        → M ↝ N

      CastVote :
          h ⊢ M ⇉ N
          ---------
        → M ↝ N

      CreateBlock :
          h ⊢ M ↷ N
          ---------
        → M ↝ N

      NextSlot :
          Delivered M
          -----------
        → M ↝ tick M
```

### Reflexive, transitive closure

```agda
    infix  2 _↝⋆_
    infixr 2 _∷′_
    infix  3 []′

    data _↝⋆_ : State → State → Set where
      []′ : M ↝⋆ M
      _∷′_ : M ↝ N → N ↝⋆ O → M ↝⋆ O
```
<!--
### Composition
```agda
    ↝⋆∘↝⋆ :
        M ↝⋆ N
      → N ↝⋆ O
      → M ↝⋆ O
    ↝⋆∘↝⋆ []′ M↝⋆O = M↝⋆O
    ↝⋆∘↝⋆ (M↝M₁ ∷′ M₁↝⋆N) N↝⋆O = M↝M₁ ∷′ ↝⋆∘↝⋆ M₁↝⋆N N↝⋆O
```
### Post-composition
```agda
    ↝∘↝⋆ :
        M ↝⋆ N
      → N ↝ O
      → M ↝⋆ O
    ↝∘↝⋆ []′ N↝O =  N↝O ∷′ []′
    ↝∘↝⋆ (M↝M₁ ∷′ M₁↝⋆N) N↝O = M↝M₁ ∷′ ↝∘↝⋆ M₁↝⋆N N↝O
```
-->

## Collision free predicate

<!--
```agda
    open State
```
-->

Rather than assuming a global axiom on the injectivity of the hash function
or that any reachable state is collision-free, there is a predicate assuming
that there are no hash collisions during the execution of the protocol.

```agda
    data CollisionFree (N : State) : Set where

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
    []↷-hist-common-prefix {M} (honest-cooldown {block = b} refl _ _ _ _ _ _) = xs⊆x∷xs (history M) (BlockMsg b)

    []⇉-hist-common-prefix : ∀ {M N p} {h : Honesty p}
      → h ⊢ M ⇉ N
      → history M ⊆ₘ history N
    []⇉-hist-common-prefix {M} (honest {vote = v} refl _ _ _ _ _) = xs⊆x∷xs (history M) (VoteMsg v)

    []↷-collision-free : ∀ {M N p} {h : Honesty p}
      → CollisionFree N
      → h ⊢ M ↷ N
      → CollisionFree M
    []↷-collision-free cf-N M[]↷N = collision-free-resp-⊇ cf-N ([]↷-hist-common-prefix M[]↷N)

    []⇉-collision-free : ∀ {M N p} {h : Honesty p}
      → CollisionFree N
      → h ⊢ M ⇉ N
      → CollisionFree M
    []⇉-collision-free cf-N M[]⇉N = collision-free-resp-⊇ cf-N ([]⇉-hist-common-prefix M[]⇉N)
```
-->

### Properties

When the current state is collision free, the pervious state was so too

```agda
    ↝-collision-free : ∀ {N₁ N₂ : State}
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
    ↝-collision-free (NextSlot _) (collision-free x) = collision-free x
```
-->

When the current state is collision free, previous states were so too

```agda
    ↝⋆-collision-free : ∀ {N₁ N₂ : State}
      → N₁ ↝⋆ N₂
      → CollisionFree N₂
        ----------------
      → CollisionFree N₁
```
<!--
```agda
    ↝⋆-collision-free ([]′) N = N
    ↝⋆-collision-free (N₁↝N₂ ∷′ N₂↝⋆N₃) N₃ =
      ↝-collision-free N₁↝N₂ (↝⋆-collision-free N₂↝⋆N₃ N₃)
```
-->

## Forging free predicate

Signatures are not modelled explicitly. Instead we assume that the adversary
cannot send any block with the `creatorId` of an honest party that is not
already in the block history.

```agda
    data ForgingFree (N : State) : Set where

      forging-free : ∀ {M : State} {b} {p}
        → Corrupt {p} ⊢ M ↷ N
        → All (λ { m → (m ≡ BlockMsg b × HonestBlock b)
            → m ∈ history M }) (history N)
        → ForgingFree N
```
