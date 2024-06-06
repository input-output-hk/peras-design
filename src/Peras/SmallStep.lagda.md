```agda
module Peras.SmallStep where
```

<!--
```agda
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.List as List using (List; all; foldr; _∷_; []; _++_; filter; filterᵇ; map; cartesianProduct; length; head; catMaybes; any)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Any using (Any; _─_; _∷=_; any?)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (suc; pred; _≤_; _<_; _≤ᵇ_; _≤?_; _<?_; _≥_; _≥?_; ℕ; _+_; _*_; _∸_; _≟_; _>_;_<ᵇ_)
open import Data.Fin using (Fin; zero; suc) renaming (pred to decr)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂; curry; uncurry)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)

open import Function using (_∘_; id; _$_; flip)
open import Relation.Binary.Bundles using (StrictTotalOrder)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym; subst; trans)
open import Relation.Nullary using (yes; no; ¬_; Dec)
open import Relation.Nullary.Decidable using (⌊_⌋; ¬?; _⊎-dec_; _×-dec_)
open import Relation.Nullary.Negation using (contradiction; contraposition)

open import Prelude.AssocList hiding (_∈_)
open Decidable _≟_

open import Peras.Block
open import Peras.Chain
open import Peras.Crypto
open import Peras.Numbering
open import Peras.Params

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
leadership and voting committee membership) and the cryptographic signatures.
The parameters for the Peras protocol and hash functions are defined as instance
arguments of the module.

```agda
module _ ⦃ _ : Hashable Block ⦄
         ⦃ _ : Hashable (List Tx) ⦄
         ⦃ _ : Params ⦄
         ⦃ _ : Network ⦄
         ⦃ _ : Postulates ⦄

         where
```
  The block tree, resp. the validity of the chain is defined with respect of the
  parameters.
```agda
  open Hashable ⦃...⦄
  open Params ⦃...⦄
  open Network ⦃...⦄
  open Postulates ⦃...⦄
```
#### Messages

Messages for sending and receiving blocks and votes. In the `Peras` protocol
certificates are not diffused explicitly with the exception of bootstraping the
system.
```agda
  data Message : Set where
    ChainMsg : ∀ {c : Chain} → ValidChain c → Message
    VoteMsg : Vote → Message
```
<!--
```agda
{-
  Message-injective : ∀ {b₁ b₂}
    → ChainMsg b₁ ≡ ChainMsg b₂
    → b₁ ≡ b₂
  Message-injective refl = refl
-}
```
```agda
{-
  Message-injective′ : ∀ {b₁ b₂}
    → b₁ ≢ b₂
    → ChainMsg b₁ ≢ ChainMsg b₂
  Message-injective′ = contraposition Message-injective
-}
```
Messages can be delayed by a number of slots
```agda
  Delay = Fin (suc (suc Δ))
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
#### Block-tree

A block-tree is defined by properties - an implementation of the block-tree
has to fulfil all the properties mentioned below:

```agda
  record IsTreeType {T : Set}
                    (tree₀ : T)
                    (newChain : ∀ {c : Chain} → T → ValidChain c → T)
                    (allBlocks : T → List Block)
                    (preferredChain : T → Chain)
                    (addVote : T → Vote → T)
                    (votes : T → List Vote)
                    (certs : T → List Certificate)
                    (cert₀ : Certificate)
         : Set₁ where

    field
```
Properties that must hold with respect to blocks and votes.

**TODO**: Use the properties (A1) - (A9) of the block-tree with certificates instead
as proposed in the paper.

```agda
      instantiated :
        allBlocks tree₀ ≡ block₀ ∷ []

      instantiated-certs :
        certs tree₀ ≡ cert₀ ∷ []

      genesis-block-slotnumber :
        getSlotNumber (slotNumber block₀) ≡ 0

      genesis-cert-roundnumber :
        getRoundNumber (round cert₀) ≡ 0

      extendable-votes : ∀ (t : T) (v : Vote)
        → allBlocks (addVote t v) ≐ allBlocks t

      valid : ∀ (t : T)
        → ValidChain (preferredChain t)

      optimal : ∀ (c : Chain) (t : T)
        → let b = preferredChain t
              cts = certs t
          in
          ValidChain c
        → c ⊆ allBlocks t
        → ∥ c ∥ cts ≤ ∥ b ∥ cts

      self-contained : ∀ (t : T)
        → preferredChain t ⊆ allBlocks t

      valid-votes : ∀ (t : T)
        → All ValidVote (votes t)

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

      quorum-cert : ∀ (t : T) (b : Block) (r : ℕ)
        → length (filter (λ {v →
                    (getRoundNumber (votingRound v) ≟ r)
              ×-dec (blockHash v ≟-BlockHash hash b)}
            ) (votes t)) ≥ τ
        → Any (λ {c →
            (getRoundNumber (round c) ≡ r)
          × (blockRef c ≡ hash b) }) (certs t)
```
In addition to blocks the block-tree manages votes and certificates as well.
The block tree type is defined as follows:
```agda
  record TreeType (T : Set) : Set₁ where

    field
      tree₀ : T
      newChain : ∀ {c : Chain} → T → ValidChain c → T
      allBlocks : T → List Block
      preferredChain : T → Chain

      addVote : T → Vote → T

      votes : T → List Vote
      certs : T → List Certificate

    cert₀ : Certificate
    cert₀ = MkCertificate (MkRoundNumber 0) (hash block₀)

    field
      is-TreeType : IsTreeType
                      tree₀ newChain allBlocks preferredChain
                      addVote votes certs cert₀

    latestCertOnChain : T → Certificate
    latestCertOnChain =
      latestCert cert₀ ∘ catMaybes ∘ map certificate ∘ preferredChain

    latestCertSeen : T → Certificate
    latestCertSeen = latestCert cert₀ ∘ certs

    hasCert : RoundNumber → T → Set
    hasCert (MkRoundNumber r) = Any ((r ≡_) ∘ roundNumber) ∘ certs

    hasCert? : (r : RoundNumber) (t : T) → Dec (hasCert r t)
    hasCert? (MkRoundNumber r) = any? ((r ≟_) ∘ roundNumber) ∘ certs

    hasVote : RoundNumber → T → Set
    hasVote (MkRoundNumber r) = Any ((r ≡_) ∘ votingRound') ∘ votes

    hasVote? : (r : RoundNumber) (t : T) → Dec (hasVote r t)
    hasVote? (MkRoundNumber r) = any? ((r ≟_) ∘ votingRound') ∘ votes

    preferredChain′ : SlotNumber → T → Chain
    preferredChain′ (MkSlotNumber sl) =
      let cond = (_≤? sl) ∘ slotNumber'
      in filter cond ∘ preferredChain
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
           {parties : Parties} -- TODO: use parties from blockTrees

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

      ChainReceived : ∀ {b t} {c : ValidChain b}
          ------------------------------
        → t [ ChainMsg c ]→ newChain t c
```
#### Vote in round

When does a party vote in a round? The protocol expects regular voting, i.e. if
in the previous round a quorum has been achieved or that voting resumes after a
cool-down phase.
```agda
    data VoteInRound : RoundNumber → T → Set where

      Regular : ∀ {r t} →
        let
          pref  = preferredChain t
          cert′ = latestCertSeen t
        in
          r ≡ (roundNumber cert′) + 1       -- VR-1A
        → cert′ PointsInto pref             -- VR-1B
          -------------------------------
        → VoteInRound (MkRoundNumber r) t

      AfterCooldown : ∀ {r c t} →
        let
          cert⋆ = latestCertOnChain t
          cert′ = latestCertSeen t
        in
          c > 0
        → r ≥ (roundNumber cert′) + R       -- VR-2A
        → r ≡ (roundNumber cert⋆) + (c * K) -- VR-2B
          ---------------------------------
        → VoteInRound (MkRoundNumber r) t
```
### State

The small-step semantics rely on a global state, which consists of the following fields:

* Current slot of the system
* Map with local state per party
* All the messages that have been sent but not yet been delivered
* All the messages that have been sent
* Adversarial state

```agda
    record State : Set where
      constructor ⟦_,_,_,_,_⟧
      field
        clock : SlotNumber
        blockTrees : AssocList PartyId T
        messages : List Envelope
        history : List Message
        adversarialState : S

      blockTrees' : List T
      blockTrees' = map proj₂ blockTrees

      v-rnd : RoundNumber
      v-rnd = v-round clock

      v-rnd' : ℕ
      v-rnd' = getRoundNumber v-rnd
```
#### Progress

Rather that keeping track of progress, we introduce a predicate stating that all
messages that are not delayed have been delivered. This is a precondition that
must hold before transitioning to the next slot.
```agda
    Fetched : State → Set
    Fetched = All (λ { z → delay z ≢ zero }) ∘ messages
      where open State
```
```agda
    LastSlotInRound : State → Set
    LastSlotInRound M =
      suc (rnd (getSlotNumber clock)) ≡ rnd (suc (getSlotNumber clock))
      where open State M
```
```agda
    NextSlotInSameRound : State → Set
    NextSlotInSameRound M =
      rnd (getSlotNumber clock) ≡ rnd (suc (getSlotNumber clock))
      where open State M
```
```agda
    RequiredVotes : State → Set
    RequiredVotes M =
      let r = v-round clock
       in Any (VoteInRound r ∘ proj₂) blockTrees
        → Any (hasVote r ∘ proj₂) blockTrees
      where open State M
```
Ticking the global clock increments the slot number and decrements the delay of
all the messages in the message buffer.
```agda
    tick : State → State
    tick M =
      record M
        { clock = next clock
        ; messages =
            map (λ where e → record e { delay = decr (delay e) })
              messages
        }
      where open State M
```
Updating the global state inserting the updated block-tree for a given party,
adding messages to the message buffer for the other parties and appending the
history. "add and diffuse" from the paper
```agda
    _,_,_,_⇑_ : Message → Delay → PartyId → T → State → State
    m , d , p , l ⇑ M =
      record M
        { blockTrees = (p , l) ↑ blockTrees
        ; messages =
            map (uncurry ⦅_,_, m , d ⦆)
              (filter (¬? ∘ (p ≟_) ∘ proj₁) parties)
            ++ messages
        ; history = m ∷ history
        }
      where open State M

    add_to_diffuse_ : (Message × Delay × PartyId) → T → State → State
    add (m@(ChainMsg x) , d , p) to t diffuse M = m , d , p , newChain t x ⇑ M
    add (m@(VoteMsg x) , d , p) to t diffuse M = m , d , p , addVote t x ⇑ M
```
## Fetching

A party receives messages from the global state by fetching messages assigned to
the party, updating the local block tree and putting the local state back into
the global state.

```agda
    data _⊢_[_]⇀_ : {p : PartyId} → Honesty p → State → Message → State → Set
      where
```
An honest party consumes a message from the global message buffer and updates
the local state
```agda
      honest : ∀ {p} {t t′} {m} {N}
        → let open State N in
          p ‼ blockTrees ≡ just t
        → (m∈ms : ⦅ p , Honest , m , zero ⦆ ∈ messages)
        → t [ m ]→ t′
          ------------------------------------------------
        → Honest {p} ⊢
          N [ m ]⇀ record N
            { blockTrees = (p , t′) ↑ blockTrees
            ; messages = messages ─ m∈ms
            }
```
An adversarial party might delay a message
```agda
      corrupt : ∀ {p} {as} {m} {N}
        → let open State N in
          (m∈ms : ⦅ p , Corrupt , m , zero ⦆ ∈ messages)
          -------------------------------------------------
        → Corrupt {p} ⊢
          N [ m ]⇀ record N
            { messages = m∈ms ∷= ⦅ p , Corrupt , m , suc zero ⦆
            ; adversarialState = as
            }
```
## Voting

A party can cast a vote for a block, if
  * the current slot is the first slot in a voting round
  * the party is a member of the voting committee
  * the chain is not in a cool-down phase

Voting updates the party's local state and for all other parties a message
is added to be consumed immediately.
```agda
    infix 2 _⊢_⇉_

    data _⊢_⇉_ : {p : PartyId} → Honesty p → State → State → Set where

      honest : ∀ {p} {t} {M} {prf} {sig} {vote}
        → let open State M
              open IsTreeType
              Cpref = valid is-TreeType t
              r = v-round clock
              v = record
                    { votingRound = r
                    ; creatorId = p
                    ; proofM = prf
                    ; blockHash = hash $ tip Cpref -- FIXME: Preagreement, (clock earlierBy L) t
                    ; signature = sig
                    }
          in
          vote ≡ v
        → p ‼ blockTrees ≡ just t
        → IsVoteSignature v sig
        → StartOfRound clock r
        → IsCommitteeMember p r prf
        → VoteInRound r t
          -------------------------------------
        → Honest {p} ⊢
            M ⇉ add (VoteMsg v , zero , p) to t
                diffuse M
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
    infix 2 _⊢_↷_
```
During regular execution of the protocol, i.e. not in cool-down phase, no
certificate reference is included in the block. The exact conditions to
decide wheter a certificate has to be included are (see: Block creation in
Figure 2)
```agda
    needCert : ℕ → T → Maybe Certificate
    needCert r t =
      let cert⋆ = latestCertOnChain t
          cert′ = latestCertSeen t
      in if not (any (λ {c → ⌊ roundNumber c + 2 ≟ r ⌋}) (certs t)) -- (a)
          ∧ (r ≤ᵇ A + roundNumber cert′)                            -- (b)
          ∧ (roundNumber cert⋆ <ᵇ roundNumber cert′)                -- (c)
        then just cert′
        else nothing
```
```agda
    data _⊢_↷_ : {p : PartyId} → Honesty p → State → State → Set where

      honest : ∀ {p} {t} {M} {prf} {sig} {block}
        → let open State M
              open IsTreeType
              Cpref = valid is-TreeType t
              (hl , ht) = uncons Cpref
              r = getRoundNumber (v-round clock)
              b = record
                    { slotNumber = clock
                    ; creatorId = p
                    ; parentBlock = hash $ tip Cpref
                    ; certificate = needCert r t
                    ; leadershipProof = prf
                    ; bodyHash =
                        let txs = txSelection clock p
                        in blockHash
                             record
                               { blockHash = hash txs
                               ; payload = txs
                               }
                    ; signature = sig
                    }
              cert⋆ = latestCertOnChain t
              cert′ = latestCertSeen t
          in
          block ≡ b
        → p ‼ blockTrees ≡ just t
        → (bs : IsBlockSignature b sig)
        → (sl : IsSlotLeader p clock prf)
          ---------------------------------------------------------------
        → Honest {p} ⊢
            M ↷ add (ChainMsg (Cons bs sl refl ht Cpref) , zero , p) to t
                diffuse M
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
* Fetching messages at the beginning of each slot
* Block creation
* Voting
* Transition to next slot
```agda
    data _↝_ : State → State → Set where

      Fetch : ∀ {m}
        → h ⊢ M [ m ]⇀ N
          --------------
        → M ↝ N

      CreateVote :
          Fetched M
        → h ⊢ M ⇉ N
          ---------
        → M ↝ N

      CreateBlock :
          Fetched M
        → h ⊢ M ↷ N
          ---------
        → M ↝ N

      NextSlot :
          Fetched M
        → NextSlotInSameRound M
          ---------------------
        → M ↝ tick M

      NextSlotNewRound :
          Fetched M
        → LastSlotInRound M
        → RequiredVotes M
          ---------------
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
Transitions of voting rounds
```agda
    data _↦_ : State → State → Set where

      NextRound : let open State in
          suc (v-rnd' M) ≡ v-rnd' N
        → M ↝⋆ N
        → M ↦ N
```
```agda
    infix  2 _↦⋆_
    infixr 2 _∷″_
    infix  3 []″

    data _↦⋆_ : State → State → Set where
      []″ : M ↦⋆ M
      _∷″_ : M ↦ N → N ↦⋆ O → M ↦⋆ O
```
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
{-
    data CollisionFree (N : State) : Set where

      collision-free : ∀ {b₁ b₂ : Block}
        → All
          (λ { (m₁ , m₂) → m₁ ≡ BlockMsg b₁ → m₂ ≡ BlockMsg b₂ →
               (hash b₁ ≡ hash b₂ → b₁ ≡ b₂) })
          (cartesianProduct (history N) (history N))
        → CollisionFree N
-}
```

<!--
```agda
{-
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
-}
```
-->

### Properties

When the current state is collision free, the pervious state was so too

```agda
{-
    ↝-collision-free :
        M ↝ N
      → CollisionFree N
        ----------------
      → CollisionFree M
-}
```
<!--
```agda
{-
    ↝-collision-free (Fetch x) cf-N = []⇀-collision-free cf-N x
    ↝-collision-free (CreateVote _ x) cf-N = []⇉-collision-free cf-N x
    ↝-collision-free (CreateBlock _ x) cf-N =  []↷-collision-free cf-N x
    ↝-collision-free (NextSlot _ _) (collision-free x) = collision-free x
    ↝-collision-free (NextSlotNewRound _ _ _) (collision-free x) = collision-free x
-}
```
-->

When the current state is collision free, previous states were so too

```agda
{-
    ↝⋆-collision-free :
        M ↝⋆ N
      → CollisionFree N
        ----------------
      → CollisionFree M
-}
```
<!--
```agda
{-
    ↝⋆-collision-free ([]′) N = N
    ↝⋆-collision-free (M↝N ∷′ N↝⋆O) O =
      ↝-collision-free M↝N (↝⋆-collision-free N↝⋆O O)
-}
```
-->

## Forging free predicate

Signatures are not modelled explicitly. Instead we assume that the adversary
cannot send any block with the `creatorId` of an honest party that is not
already in the block history.

```agda
{-
    data ForgingFree (N : State) : Set where

      forging-free : ∀ {M : State} {b} {p}
        → Corrupt {p} ⊢ M ↷ N
        → All (λ { m → (m ≡ BlockMsg b × HonestBlock b)
            → m ∈ history M }) (history N)
        → ForgingFree N
-}
```
