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
open import Prelude.Init hiding (_⊆_)

open Nat using (_≟_; _≤?_; _≤ᵇ_; _≥?_; _%_; _>?_; NonZero)
open L using (concat)
open L.All using (All)
open L.Any using (Any; _─_; any?) renaming (_∷=_ to _∷ˡ=_)

open import Peras.Block
open import Peras.Chain
open import Peras.Crypto hiding (_≟_)
open import Peras.Numbering
open import Peras.Params

open import Data.List.Relation.Binary.Subset.Propositional {A = Block} using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional {A = Certificate} renaming (_⊆_ to _⊆ᶜ_)

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

* Adaptively Secure Fast Settlement Supporting Dynamic Participation and Self-Healing
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
  data Message : Type where
    ChainMsg : Chain → Message
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

  pattern 𝟘 = fzero
  pattern 𝟙 = fsuc fzero
  pattern 𝟚 = fsuc (fsuc fzero)
```
Messages are put into an envelope and assigned to a party. The message can be
delayed.
```agda
  record Envelope : Type where
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
  record IsTreeType {T : Type}
                    (tree₀ : T)
                    (newChain : T → Chain → T)
                    (allChains : T → List Chain)
                    (preferredChain : T → Chain)
                    (addVote : T → Vote → T)
                    (votes : T → List Vote)
                    (certs : T → List Certificate)
                    (cert₀ : Certificate)
         : Type₁ where

    field
```
Properties that must hold with respect to chains, certificates and votes.

**TODO**: Use the properties (A1) - (A9) of the block-tree with certificates instead
as proposed in the paper.

```agda
      instantiated :
        preferredChain tree₀ ≡ block₀ ∷ []

      instantiated-certs :
        certs tree₀ ≡ cert₀ ∷ []

      instantiated-votes :
        votes tree₀ ≡ []

      genesis-block-slotnumber :
        getSlotNumber (slotNumber block₀) ≡ 0

      genesis-block-no-certificate :
        certificate block₀ ≡ nothing

      extendable-chain : ∀ (t : T) (c : Chain)
        → certs (newChain t c) ≡ certsFromChain c ++ certs t

      valid : ∀ (t : T)
        → ValidChain (preferredChain t)

      optimal : ∀ (c : Chain) (t : T)
        → let
            b = preferredChain t
            cts = certs t
          in
          ValidChain c
        → c ∈ allChains t
        → ∥ c ∥ cts ≤ ∥ b ∥ cts

      self-contained : ∀ (t : T)
        → preferredChain t ∈ allChains t

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
In addition to chains the block-tree manages votes and certificates as well.
The block-tree type is defined as follows:
```agda
  record TreeType (T : Type) : Type₁ where

    field
      tree₀ : T
      newChain : T → Chain → T
      allChains : T → List Chain
      preferredChain : T → Chain

      addVote : T → Vote → T

      votes : T → List Vote
      certs : T → List Certificate

    cert₀ : Certificate
    cert₀ = MkCertificate (MkRoundNumber 0) (hash block₀)

    field
      is-TreeType : IsTreeType
                      tree₀ newChain allChains preferredChain
                      addVote votes certs cert₀

    latestCertOnChain : T → Certificate
    latestCertOnChain =
      latestCert cert₀ ∘ catMaybes ∘ map certificate ∘ preferredChain

    latestCertSeen : T → Certificate
    latestCertSeen = latestCert cert₀ ∘ certs

    hasCert : RoundNumber → T → Type
    hasCert (MkRoundNumber r) = Any ((r ≡_) ∘ roundNumber) ∘ certs

    hasCert? : (r : RoundNumber) (t : T) → Dec (hasCert r t)
    hasCert? (MkRoundNumber r) = any? ((r ≟_) ∘ roundNumber) ∘ certs

    hasVote : RoundNumber → T → Type
    hasVote (MkRoundNumber r) = Any ((r ≡_) ∘ votingRound') ∘ votes

    hasVote? : (r : RoundNumber) (t : T) → Dec (hasVote r t)
    hasVote? (MkRoundNumber r) = any? ((r ≟_) ∘ votingRound') ∘ votes

    preferredChain′ : SlotNumber → T → Chain
    preferredChain′ (MkSlotNumber sl) =
      let cond = (_≤? sl) ∘ slotNumber'
      in filter cond ∘ preferredChain

    allBlocks : T → List Block
    allBlocks = concat ∘ allChains
```
### Additional parameters

In order to define the semantics the following parameters are required
additionally:

  * The type of the block-tree
  * adversarialState₀ is the initial adversarial state
  * Tx selection function per party and slot number
  * The list of parties

```agda
  module _ {T : Type} {blockTree : TreeType T}
           {S : Type} {adversarialState₀ : S}
           {txSelection : SlotNumber → PartyId → List Tx}
           {parties : Parties} -- TODO: use parties from blockTrees
                               -- i.e. allow dynamic participation

           where

    open TreeType blockTree

    instance
      Default-T : Default T
      Default-T .def = tree₀
```
#### Block-tree update

Updating the block-tree upon receiving a message for vote and block messages.

```agda
    data _[_]→_ : T → Message → T → Type where

      VoteReceived : ∀ {v t} →
          ────────────────────────────
          t [ VoteMsg v ]→ addVote t v

      ChainReceived : ∀ {c t} →
          ──────────────────────────────
          t [ ChainMsg c ]→ newChain t c
```
#### Vote in round

When does a party vote in a round? The protocol expects regular voting, i.e. if
in the previous round a quorum has been achieved or that voting resumes after a
cool-down phase.

#### Voting rules

VR-1A: A party has seen a certificate cert-r−1 for round r−1
```agda
    VotingRule-1A : RoundNumber → T → Set
    VotingRule-1A (MkRoundNumber r) t = r ≡ roundNumber (latestCertSeen t) + 1

    VotingRule-1A? : (r : RoundNumber) → (t : T) → Dec (VotingRule-1A r t)
    VotingRule-1A? (MkRoundNumber r) t = r ≟ roundNumber (latestCertSeen t) + 1
```
VR-1B: The  extends the block certified by cert-r−1,
```agda
    VotingRule-1B : T → Set
    VotingRule-1B t = (latestCertSeen t) PointsInto (preferredChain t)

    VotingRule-1B? : (t : T) → Dec (VotingRule-1B t)
    VotingRule-1B? t = (latestCertSeen t) PointsInto? (preferredChain t)
```
VR-2A: The last certificate a party has seen is from a round at least R rounds back
```agda
    VotingRule-2A : RoundNumber → T → Set
    VotingRule-2A (MkRoundNumber r) t = r ≥ roundNumber (latestCertSeen t) + R

    VotingRule-2A? : (r : RoundNumber) → (t : T) → Dec (VotingRule-2A r t)
    VotingRule-2A? (MkRoundNumber r) t = r ≥? roundNumber (latestCertSeen t) + R
```
VR-2B: The last certificate included in a party's current chain is from a round exactly
c⋆K rounds ago for some integer c ≥ 0
<!--
```agda
    _mod_ : ℕ → (n : ℕ) → ⦃ NonZero n ⦄ → ℕ
    _mod_ a b ⦃ prf ⦄ = _%_ a b ⦃ prf ⦄
```
-->
```agda
    VotingRule-2B : RoundNumber → T → Set
    VotingRule-2B (MkRoundNumber r) t =
        r > roundNumber (latestCertOnChain t)
      × r mod K ≡ (roundNumber (latestCertOnChain t)) mod K

    VotingRule-2B? : (r : RoundNumber) → (t : T) → Dec (VotingRule-2B r t)
    VotingRule-2B? (MkRoundNumber r) t =
            r >? roundNumber (latestCertOnChain t)
      ×-dec r mod K ≟ (roundNumber (latestCertOnChain t)) mod K
```
If either VR-1A and VR-1B or VR-2A and VR-2B hold, voting is expected
```agda
    data VoteInRound : RoundNumber → T → Type where

      Regular : ∀ {r t} →
        ∙ VotingRule-1A r t
        ∙ VotingRule-1B t
          ─────────────────
          VoteInRound r t

      AfterCooldown : ∀ {r t} →
        ∙ VotingRule-2A r t
        ∙ VotingRule-2B r t
          ─────────────────
          VoteInRound r t
```
Decidablity for the `VotingInRound` relation
```agda
    vr-1a-2a : ∀ {r : RoundNumber} → {t : T} → (¬ VotingRule-1A r t) × (¬ VotingRule-2A r t)  → ¬ VoteInRound r t
    vr-1a-2a (x₁ , _) (Regular y₁ _) = contradiction y₁ x₁
    vr-1a-2a (_ , x₂) (AfterCooldown y₁ _) = contradiction y₁ x₂

    vr-1a-2b : ∀ {r : RoundNumber} → {t : T} → (¬ VotingRule-1A r t) × (¬ VotingRule-2B r t)  → ¬ VoteInRound r t
    vr-1a-2b (x₁ , _) (Regular y₁ _) = contradiction y₁ x₁
    vr-1a-2b (_ , x₂) (AfterCooldown _ y₂) = contradiction y₂ x₂

    vr-1b-2a : ∀ {r : RoundNumber} → {t : T} → (¬ VotingRule-1B t) × (¬ VotingRule-2A r t)  → ¬ VoteInRound r t
    vr-1b-2a (x₁ , _) (Regular _ y₂) = contradiction y₂ x₁
    vr-1b-2a (_ , x₂) (AfterCooldown y₁ _) = contradiction y₁ x₂

    vr-1b-2b : ∀ {r : RoundNumber} → {t : T} → (¬ VotingRule-1B t) × (¬ VotingRule-2B r t)  → ¬ VoteInRound r t
    vr-1b-2b (x₁ , _) (Regular _ y₂) = contradiction y₂ x₁
    vr-1b-2b (_ , x₂) (AfterCooldown _ y₂) = contradiction y₂ x₂
```
```agda
    VoteInRound? : (r : RoundNumber) → (t : T) → Dec (VoteInRound r t)
    VoteInRound? r t
      with VotingRule-1A? r t
         | VotingRule-1B? t
         | VotingRule-2A? r t
         | VotingRule-2B? r t
    ... | yes p | yes q | _     | _     = yes $ Regular p q
    ... | _     | _     | yes p | yes q = yes $ AfterCooldown p q
    ... | no p  | _     | no q  | _     = no  $ vr-1a-2a (p , q)
    ... | no p  | _     | _     | no q  = no  $ vr-1a-2b (p , q)
    ... | _     | no p  | no q  | _     = no  $ vr-1b-2a (p , q)
    ... | _     | no p  | _     | no q  = no  $ vr-1b-2b (p , q)
```
### State

The small-step semantics rely on a global state, which consists of the following fields:

* Current slot of the system
* Map with local state per party
* All the messages that have been sent but not yet been delivered
* All the messages that have been sent
* Adversarial state

```agda
    record State : Type where
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

Rather than keeping track of progress, we introduce a predicate stating that all
messages that are not delayed have been delivered. This is a precondition that
must hold before transitioning to the next slot.
```agda
    Fetched : State → Type
    Fetched = All (λ { z → delay z ≢ 𝟘 }) ∘ messages
      where open State
```
Predicate for a global state stating that the current slot is the last slot of
a voting round.
```agda
    LastSlotInRound : State → Type
    LastSlotInRound M =
      suc (rnd (getSlotNumber clock)) ≡ rnd (suc (getSlotNumber clock))
      where open State M
```
Predicate for a global state stating that the next slot will be in a new voting
round.
```agda
    NextSlotInSameRound : State → Type
    NextSlotInSameRound M =
      rnd (getSlotNumber clock) ≡ rnd (suc (getSlotNumber clock))
      where open State M
```
Predicate for a global state asserting that parties of the voting committee for
a the current voting round have voted. This is needed as a condition when
transitioning from one voting round to another.

**TODO**: Properly define the condition for required votes
```agda
    RequiredVotes : State → Type
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
            map (λ where e → record e { delay = pred (delay e) })
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
        { blockTrees = set p l blockTrees
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
    data _⊢_[_]⇀_ : {p : PartyId} → Honesty p → State → Message → State → Type
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
        →  Corrupt {p} ⊢
          N [ m ]⇀ record N
            { messages = m∈ms ∷ˡ= ⦅ p , Corrupt , m , 𝟙 ⦆
            ; adversarialState = as
            }
```
## Voting
#### Preagreement
**TODO**: Needs to be finalized in the Peras paper
```agda
    Preagreement : SlotNumber → T → Block
    Preagreement (MkSlotNumber s) t =
      let
        Cpref = preferredChain t
        bs = filter (λ {b → (slotNumber' b) ≤? (s ∸ L)}) Cpref
      in fromMaybe block₀ (head bs)
```
Helper function for creating a vote
```agda
    createVote : SlotNumber → PartyId → MembershipProof → Signature → T → Vote
    createVote s p prf sig t =
      record
        { votingRound = v-round s
        ; creatorId = p
        ; proofM = prf
        ; blockHash =
            let b = Preagreement s t
            in hash b
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

    data _⊢_⇉_ : {p : PartyId} → Honesty p → State → State → Type where

      honest : ∀ {p} {t} {M} {π} {σ}
        → let
            open State
            s = clock M
            r = v-round s
            v = createVote s p π σ t
          in
        ∙ blockTrees M ⁉ p ≡ just t
        ∙ IsVoteSignature v σ
        ∙ StartOfRound s r
        ∙ IsCommitteeMember p r π
        ∙ VoteInRound r t
          ───────────────────────────────────
          Honest {p} ⊢
            M ⇉ add (VoteMsg v , 𝟘 , p) to t
                diffuse M
```
Rather than creating a delayed vote, an adversary can honestly create it and
delay the message.

## Block creation

Certificates are conditionally added to a block. The following function deterimes
if there needs to be a certificate provided for a given voting round and a local
block-tree.

The conditions (a) - (c) are reflected in Figure 2 in the *Peras*
paper

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
        if not (any (λ {c → ⌊ roundNumber c + 2 ≟ r ⌋}) (certs t)) -- (a)
           ∧ (r ≤ᵇ A + roundNumber cert′)                          -- (b)
           ∧ (roundNumber cert⋆ <ᵇ roundNumber cert′)              -- (c)
        then just cert′
        else nothing
```
Helper function for creating a block
```agda
    createBlock : SlotNumber → PartyId → LeadershipProof → Signature → T → Block
    createBlock s p π σ t =
      record
        { slotNumber = s
        ; creatorId = p
        ; parentBlock =
            let open IsTreeType
                (h , _) , _ = uncons (is-TreeType .valid t)
            in hash h
        ; certificate =
            let r = v-round s
            in needCert r t
        ; leadershipProof = π
        ; bodyHash =
            let txs = txSelection s p
            in blockHash
                 record
                   { blockHash = hash txs
                   ; payload = txs
                   }
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

    data _⊢_↷_ : {p : PartyId} → Honesty p → State → State → Type where

      honest : ∀ {p} {t} {M} {π} {σ}
        → let
            open State
            s = clock M
            b = createBlock s p π σ t
            pref = preferredChain t
          in
        ∙ blockTrees M ⁉ p ≡ just t
        ∙ ValidChain (b ∷ pref)
          ───────────────────────────
          Honest {p} ⊢
            M ↷ add (
                  ChainMsg (b ∷ pref)
                , 𝟘
                , p) to t
                diffuse M
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
    data _↝_ : State → State → Type where

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
        ∙ NextSlotInSameRound M
          ─────────────────────
          M ↝ tick M

      NextSlotNewRound :
        ∙ Fetched M
        ∙ LastSlotInRound M
        ∙ RequiredVotes M
          ─────────────────
          M ↝ tick M
```
#### Reflexive, transitive closure
List-like structure for defining execution paths.
```agda
    infix  2 _↝⋆_
    infixr 2 _↣_
    infix  3 ∎

    data _↝⋆_ : State → State → Type where
      ∎ : M ↝⋆ M
      _↣_ : M ↝ N → N ↝⋆ O → M ↝⋆ O
```
<!--
### Composition
```agda
{-
    ↝⋆∘↝⋆ :
        M ↝⋆ N
      → N ↝⋆ O
      → M ↝⋆ O
    ↝⋆∘↝⋆ ∎ M↝⋆O = M↝⋆O
    ↝⋆∘↝⋆ (M↝M₁ ↣ M₁↝⋆N) N↝⋆O = M↝M₁ ↣ ↝⋆∘↝⋆ M₁↝⋆N N↝⋆O
-}
```
### Post-composition
```agda
{-
    ↝∘↝⋆ :
        M ↝⋆ N
      → N ↝ O
      → M ↝⋆ O
    ↝∘↝⋆ ∎ N↝O =  N↝O ↣ ∎
    ↝∘↝⋆ (M↝M₁ ↣ M₁↝⋆N) N↝O = M↝M₁ ↣ ↝∘↝⋆ M₁↝⋆N N↝O
-}
```
-->
### Transitions of voting rounds
Transitioning of voting rounds can be described with respect of the small-step
semantics.
```agda
    data _↦_ : State → State → Type where

      NextRound : let open State in
          suc (v-rnd' M) ≡ v-rnd' N
        → M ↝⋆ N
        → M ↦ N
```
#### Reflexive, transitive closure
List-like structure for executions for voting round transitions
```agda
    infix  2 _↦⋆_
    infixr 2 _⨾_
    infix  3 ρ

    data _↦⋆_ : State → State → Type where
      ρ : M ↦⋆ M
      _⨾_ : M ↦ N → N ↦⋆ O → M ↦⋆ O
```
<!--
## Collision free predicate

```agda
    open State
```

Rather than assuming a global axiom on the injectivity of the hash function
or that any reachable state is collision-free, there is a predicate assuming
that there are no hash collisions during the execution of the protocol.

```agda
{-
    data CollisionFree (N : State) : Type where

      collision-free : ∀ {b₁ b₂ : Block}
        → All
          (λ { (m₁ , m₂) → m₁ ≡ BlockMsg b₁ → m₂ ≡ BlockMsg b₂ →
               (hash b₁ ≡ hash b₂ → b₁ ≡ b₂) })
          (cartesianProduct (history N) (history N))
        → CollisionFree N
-}
```
-->
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
<!--
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
-->
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
<!--
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
-->
<!--
```agda
{-
    ↝⋆-collision-free ∎ N = N
    ↝⋆-collision-free (M↝N ↣ N↝⋆O) O =
      ↝-collision-free M↝N (↝⋆-collision-free N↝⋆O O)
-}
```
-->
<!--
## Forging free predicate

Signatures are not modelled explicitly. Instead we assume that the adversary
cannot send any block with the `creatorId` of an honest party that is not
already in the block history.

```agda
{-
    data ForgingFree (N : State) : Type where

      forging-free : ∀ {M : State} {b} {p}
        → Corrupt {p} ⊢ M ↷ N
        → All (λ { m → (m ≡ BlockMsg b × HonestBlock b)
            → m ∈ history M }) (history N)
        → ForgingFree N
-}
```
-->
