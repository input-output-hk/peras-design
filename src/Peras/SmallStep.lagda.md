```agda
module Peras.SmallStep where
```
<!--
```agda
open import Prelude.AssocList
open import Prelude.DecEq using (DecEq)
open import Prelude.Default using (Default)
open Default ⦃...⦄
open import Prelude.InferenceRules

open import Data.Maybe using (just; nothing)
open import Data.List.Relation.Unary.Any using () renaming (_∷=_ to _∷ˡ=_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (_%_; _≥_; _>_; _≤_; NonZero)
open import Data.List.Membership.Propositional
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Data.Product using () renaming (_,_ to _,ᵖ_)

open import Haskell.Prelude hiding (_>_)
open import Haskell.Extra.Dec

open import Peras.Block
open import Peras.Chain
open import Peras.Crypto
open import Peras.Numbering
open import Peras.Params
open import Peras.Util

open Honesty public
open MembershipProof public
open Signature public
open RoundNumber public
open Party
```
-->

# Small-step semantics

The small-step semantics of the **Ouroboros Peras** protocol define the
evolution of the global state of the system modelling *honest* and *adversarial*
parties. The number of parties is fixed during the execution of the protocol and
the list of parties has to be provided as a module parameter. In addition the
model is parameterized by the lotteries (for slot leadership and voting
committee membership) as well as the type of the block tree. Furthermore
adversarial parties share generic, adversarial state.

References:

* Formalizing Nakamoto-Style Proof of Stake, Søren Eller Thomsen and Bas Spitters

### Parameters

The parameters for the *Peras* protocol and hash functions are defined as
instance arguments of the module.

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

Messages for sending and receiving chains and votes. Note, in the *Peras* protocol
certificates are not diffused explicitly.
```agda
  data Message : Set where
    ChainMsg : {c : Chain} → ValidChain c → Message
    VoteMsg : {v : Vote} → ValidVote v → Message
```
Messages can be delayed by a number of slots
```agda
  Delay = Fin (suc (suc Δ))

  pattern 𝟘 = fzero
  pattern 𝟙 = fsuc fzero
  pattern 𝟚 = fsuc (fsuc fzero)
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
#### Block-tree

A block-tree is defined by properties - an implementation of the block-tree
has to fulfil all the properties mentioned below:
```agda
  record IsTreeType {T : Set}
                    (tree₀ : T)
                    (addChain : T → {c : Chain} → ValidChain c → T)
                    (chains : T → List Chain)
                    (preferredChain : T → Chain)
                    (addVote : T → {v : Vote} → ValidVote v → T)
                    (votes : T → List Vote)
                    (certs : T → List Certificate)
                    (cert₀ : Certificate)
         : Set₁ where

    field
```
Properties that must hold with respect to chains, certificates and votes.
```agda
      instantiated :
        preferredChain tree₀ ≡ []

      instantiated-certs :
        certs tree₀ ≡ cert₀ ∷ []

      instantiated-votes :
        votes tree₀ ≡ []

      extendable-votes : ∀ (t : T) {v : Vote} (vv : ValidVote v)
        → v ∈ votes (addVote t vv)

      extendable-chain : ∀ (t : T) {c : Chain} (vc : ValidChain c)
        → certs (addChain t vc) ≡ foldr insertCert (certs t) (certsFromChain c)

      self-contained-certs : ∀ (t : T) {c : Chain}
        → c ∈ chains t
        → certs t ≡ foldr insertCert (certs t) (certsFromChain c)

      valid : ∀ (t : T)
        → ValidChain (preferredChain t)

      optimal : ∀ (c : Chain) (t : T)
        → let
            b = preferredChain t
            cts = certs t
          in
          ValidChain c
        → c ∈ chains t
        → weight c cts ≤ weight b cts

      self-contained : ∀ (t : T)
        → preferredChain t ∈ chains t

{-
      unique-votes : ∀ (t : T) {v : Vote} (vv : ValidVote v)
        → let vs = votes t
          in
          v ∈ vs
        → vs ≡ votes (addVote t vv)

      no-equivocations : ∀ (t : T) {v : Vote} (vv : ValidVote v)
        → let vs = votes t
          in
          Any (v ∻_) vs
        → vs ≡ votes (addVote t vv)
-}
{-
      quorum-cert : ∀ (t : T) (b : Block) (r : ℕ)
        → length (filter (λ {v →
                    (getRoundNumber (votingRound v) ≟ r)
              ×-dec (blockHash v ≟-BlockHash hash b)}
            ) (votes t)) ≥ τ
        → Any (λ {c →
            (getRoundNumber (round c) ≡ r)
          × (blockRef c ≡ hash b) }) (certs t)
-}
```
In addition to chains the block-tree manages votes and certificates as well.
The block-tree type is defined as follows:
```agda
  record TreeType (T : Set) : Set₁ where

    field
      tree₀ : T

      addChain : T → {c : Chain} → ValidChain c → T
      chains : T → List Chain
      preferredChain : T → Chain

      addVote : T → {v : Vote} → ValidVote v → T
      votes : T → List Vote

      certs : T → List Certificate

      is-TreeType : IsTreeType
                      tree₀ addChain chains preferredChain
                      addVote votes certs cert₀

    latestCertOnChain : T → Certificate
    latestCertOnChain =
      latestCert cert₀ ∘ mapMaybe certificate ∘ preferredChain

    latestCertSeen : T → Certificate
    latestCertSeen = latestCert cert₀ ∘ certs

    hasCert : RoundNumber → T → Set
    hasCert (MkRoundNumber r) t = Any (λ c → r ≡ roundNumber c) (certs t)

    hasVote : RoundNumber → T → Set
    hasVote (MkRoundNumber r) t = Any (λ v → r ≡ votingRound' v) (votes t)

    allBlocks : T → List Block
    allBlocks = concat ∘ chains

    postulate -- TODO: any t is constructed based on tree₀
              --       using addVote, addChain and tree₀
              --       contains cert₀ (see instantiated-certs above)
      latestCertSeen∈certs : ∀ t → latestCertSeen t ∈ certs t
```
### Additional parameters

In order to define the semantics the following parameters are required
additionally:

  * The type of the block-tree
  * adversarialState₀ is the initial adversarial state
  * Tx selection function per party and slot number
  * The list of parties
```agda
  module Semantics
           {T : Set} {blockTree : TreeType T}
           {S : Set} {adversarialState₀ : S}
           {txSelection : SlotNumber → PartyId → List Tx}
           {parties : Parties} -- TODO: use parties from blockTrees
                               -- i.e. allow dynamic participation
           where

    open TreeType blockTree

    private
      instance
        Default-T : Default T
        Default-T .def = tree₀
```
#### Block-tree update

Updating the block-tree upon receiving a message for vote and block messages.

```agda
    data _[_]→_ : T → Message → T → Set where

      VoteReceived : ∀ {v vv t} →
          ────────────────────────────
          t [ VoteMsg {v} vv ]→ addVote t vv

      ChainReceived : ∀ {c vc t} →
          ──────────────────────────────
          t [ ChainMsg {c} vc ]→ addChain t vc
```
#### Vote in round

When does a party vote in a round? The protocol expects regular voting, i.e. if
in the previous round a quorum has been achieved or that voting resumes after a
cool-down phase.

#### BlockSelection
```agda
    BlockSelection' : SlotNumber → Chain → Hash Block
    BlockSelection' (MkSlotNumber s) = tipHash ∘ filter (λ {b → (slotNumber' b) + L <= s})

    BlockSelection : SlotNumber → T → Hash Block
    BlockSelection s = BlockSelection' s ∘ preferredChain
```
#### Voting rules

VR-1A: A party has seen a certificate cert-r−1 for round r−1
```agda
    VotingRule-1A : RoundNumber → T → Set
    VotingRule-1A r t = r ≡ nextRound (round (latestCertSeen t))
```
VR-1B: The  extends the block certified by cert-r−1,
```agda
    VotingRule-1B : SlotNumber → T → Set
    VotingRule-1B s t = Extends (BlockSelection s t) (latestCertSeen t) (chains t)
```
VR-1: Both VR-1A and VR-1B hold
```agda
    VotingRule-1 : SlotNumber → T → Set
    VotingRule-1 s t =
        VotingRule-1A (v-round s) t
      × VotingRule-1B s t
```
VR-2A: The last certificate a party has seen is from a round at least R rounds back
```agda
    VotingRule-2A : RoundNumber → T → Set
    VotingRule-2A (MkRoundNumber r) t = r ≥ roundNumber (latestCertSeen t) + R
```
VR-2B: The last certificate included in a party's current chain is from a round exactly
c⋆K rounds ago for some c : ℕ, c ≥ 0
<!--
```agda
    _mod_ : Nat → (n : Nat) → ⦃ NonZero n ⦄ → Nat
    _mod_ a b ⦃ prf ⦄ = _%_ a b ⦃ prf ⦄
```
-->
```agda
    VotingRule-2B : RoundNumber → T → Set
    VotingRule-2B (MkRoundNumber r) t =
        r > roundNumber (latestCertOnChain t)
      × r mod K ≡ (roundNumber (latestCertOnChain t)) mod K
```
VR-2: Both VR-2A and VR-2B hold
```agda
    VotingRule-2 : RoundNumber → T → Set
    VotingRule-2 r t =
        VotingRule-2A r t
      × VotingRule-2B r t
```
If either VR-1A and VR-1B or VR-2A and VR-2B hold, voting is expected
```agda
    VotingRule : SlotNumber → T → Set
    VotingRule s t =
      Either
        (VotingRule-1 s t)
        (VotingRule-2 (v-round s) t)
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

      v-rnd : RoundNumber
      v-rnd = v-round clock

      v-rnd' : Nat
      v-rnd' = getRoundNumber v-rnd
```
#### Progress

Rather than keeping track of progress, we introduce a predicate stating that all
messages that are not delayed have been delivered. This is a precondition that
must hold before transitioning to the next slot.
```agda
    Fetched : State → Set
    Fetched s = All (λ { z → delay z ≢ 𝟘 }) (messages s)
      where open State
```
Ticking the global clock increments the slot number and decrements the delay of
all the messages in the message buffer.
```agda
    tick : State → State
    tick M =
      record M
        { clock = next clock
        ; messages =
            map (λ where e → record e { delay = Data.Fin.pred (delay e) })
              messages
        }
      where open State M
```
Updating the global state inserting the updated block-tree for a given party,
adding messages to the message buffer for the other parties and appending the
history
```agda
    _,_⇑_ : Message → (PartyId → Delay) → State → State
    m , fᵈ ⇑ M =
      record M
        { messages =
            map (λ (p ,ᵖ h) → ⦅ p , h , m , fᵈ p ⦆) parties
              ++ messages

        ; history = m ∷ history
        }
      where open State M

    delay_by_update_ : Message → (PartyId → Delay) → State → State
    delay m@(ChainMsg x) by fᵈ update M = m , fᵈ ⇑ M
    delay m@(VoteMsg x) by fᵈ update M = m , fᵈ ⇑ M
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
      honest : ∀ {p} {t t′} {m} {N} → let open State N in
          blockTrees ⁉ p ≡ just t
        → (m∈ms : ⦅ p , Honest , m , 𝟘 ⦆ ∈ messages)
        → t [ m ]→ t′
          ---------------------------------------------
        → Honest {p} ⊢
          N [ m ]⇀ record N
            { blockTrees = set p t′ blockTrees
            ; messages = messages ─ m∈ms
            }
```
An adversarial party might delay a message
```agda
      corrupt : ∀ {p} {as} {m} {N} → let open State N in
          (m∈ms : ⦅ p , Corrupt , m , 𝟘 ⦆ ∈ messages)
          ----------------------------------------------
        → Corrupt {p} ⊢
          N [ m ]⇀ record N
            { messages = m∈ms ∷ˡ= ⦅ p , Corrupt , m , 𝟙 ⦆
            ; adversarialState = as
            }
```
## Voting

Helper function for creating a vote
```agda
    createVote : SlotNumber → PartyId → MembershipProof → Signature → Hash Block → Vote
    createVote s p prf sig hb =
      record
        { votingRound = v-round s
        ; creatorId = p
        ; proofM = prf
        ; blockHash = hb
        ; signature = sig
        }
```
A party can vote for a block, if
  * the current slot is the first slot in a voting round
  * the party is a member of the voting committee
  * the chain is not in a cool-down phase

Voting updates the party's local state and for all other parties a message
is added to be consumed immediately.
```agda
    infix 2 _⊢_⇉_

    data _⊢_⇉_ : {p : PartyId} → Honesty p → State → State → Set where

      honest : ∀ {p} {t} {M} {π} {σ} {b}
        → let
            open State
            s = clock M
            r = v-round s
            v = createVote s p π σ b
          in
          BlockSelection s t ≡ b
        → blockTrees M ⁉ p ≡ just t
        → (sig : IsVoteSignature v σ)
        → StartOfRound s r
        → (mem : IsCommitteeMember p r π)
        → VotingRule s t
        → (fᵈ : PartyId → Delay)
          ----------------------------------------------
        → Honest {p} ⊢
            M ⇉ delay VoteMsg (mem , sig) by fᵈ
                 update M
```
Rather than creating a delayed vote, an adversary can honestly create it and
delay the message.

## Block creation

Certificates are conditionally added to a block. The following function determines
if there needs to be a certificate provided for a given voting round and a local
block-tree. The conditions are as follows

a) There is no certificate from 2 rounds ago in certs
b) The last seen certificate is not expired
c) The last seen certificate is from a later round than
   the last certificate on chain

```agda
    needCert : RoundNumber → T → Maybe Certificate
    needCert (MkRoundNumber r) t =
      let
        cert⋆ = latestCertOnChain t
        cert′ = latestCertSeen t
      in
        if not (any (λ c → roundNumber c + 2 == r) (certs t)) -- (a)
           && (r <= A + roundNumber cert′)                    -- (b)
           && (roundNumber cert⋆ < roundNumber cert′)         -- (c)
        then Just cert′
        else Nothing
```
Helper function for creating a block
```agda
    createBlock : SlotNumber → PartyId → LeadershipProof → Signature → T → Block
    createBlock s p π σ t =
      record
        { slotNumber = s
        ; creatorId = p
        ; parentBlock = tipHash (preferredChain t)
        ; certificate = needCert (v-round s) t
        ; leadershipProof = π
        ; bodyHash = hash (txSelection s p)
        ; signature = σ
        }
```
A party can create a new block by adding it to the local block tree and
diffuse the block creation messages to the other parties. Block creation is
possible, if as in *Praos*

  * the block signature is correct
  * the party is the slot leader

Block creation updates the party's local state and for all other parties a
message is added to the message buffer
```agda
    infix 2 _⊢_↷_

    data _⊢_↷_ : {p : PartyId} → Honesty p → State → State → Set where

      honest : ∀ {p} {t} {M} {π} {σ}
        → let
            open State
            s = clock M
            b = createBlock s p π σ t
            pref = preferredChain t
          in
          blockTrees M ⁉ p ≡ just t
        → (vc : ValidChain (b ∷ pref))
        → (fᵈ : PartyId → Delay)
          ----------------------------
        → Honest {p} ⊢
            M ↷ delay ChainMsg vc by fᵈ
                 update M
```
## Small-step semantics

The small-step semantics describe the evolution of the global state.
```agda
    variable
      M N O : State
      p : PartyId
      h : Honesty p
```
The relation allows

* Fetching messages at the beginning of each slot
* Block creation
* Voting
* Transitioning to next slot in the same voting round
* Transitioning to next slot in a new voting round

Note, when transitioning to the next slot we need to distinguish whether the
next slot is in the same or a new voting round. This is necessary in order to
detect adversarial behaviour with respect to voting (adversarialy not voting
in a voting round)
```agda
    data _↝_ : State → State → Set where

      Fetch : ∀ {m} →
        ∙ h ⊢ M [ m ]⇀ N
          ──────────────
          M ↝ N

      CreateVote :
        ∙ Fetched M
        ∙ h ⊢ M ⇉ N
          ─────────
          M ↝ N

      CreateBlock :
        ∙ Fetched M
        ∙ h ⊢ M ↷ N
          ─────────
          M ↝ N

      NextSlot :
        ∙ Fetched M
          ──────────
          M ↝ tick M
```
#### Reflexive, transitive closure
List-like structure for defining execution paths.
```agda
    infix  2 _↝⋆_
    infixr 2 _↣_
    infix  3 ∎

    data _↝⋆_ : State → State → Set where
      ∎ : M ↝⋆ M
      _↣_ : M ↝ N → N ↝⋆ O → M ↝⋆ O
```
```agda
    infixr 2 _++'_

    _++'_ :
        M ↝⋆ N
      → N ↝⋆ O
      → M ↝⋆ O
    ∎ ++' M↝⋆O = M↝⋆O
    (M↝M₁ ↣ M₁↝⋆N) ++' N↝⋆O = M↝M₁ ↣ M₁↝⋆N ++' N↝⋆O
```
```agda
  open Semantics public
```
