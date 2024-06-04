# Peras: Post-Workshop Pseudocode

<!--
```agda
{-# OPTIONS --type-in-type --allow-unsolved-metas #-}
module Protocol.PerasL where

open import Effect.Monad
open import Data.Nat.DivMod using ( _div_ ; _mod_ )
open import Data.Nat hiding (_≟_ ; _>_ ; _/_ ; _≤_ ; _≥_ )
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Data.List using (foldr ; map)
open import Data.Bool hiding (_≤_)
open import Data.Maybe using (Maybe ; nothing ; just)
open import Function using (_$_)

```
-->

## Preliminaries


### Parameters

Ouroboros Peras has the following parameters:

<!--
```agda
postulate
  -- Various utility functions
  _[_] : forall {a} -> List a -> ℕ -> a

  _==_ : forall {a : Set} -> a -> a -> Bool

  _and_ : Bool -> Bool -> Bool
  _≤_ : ℕ -> ℕ -> Bool
  _≥_ : ℕ -> ℕ -> Bool
  _>_ : ℕ -> ℕ -> Bool
  _-_ : ℕ -> ℕ -> ℕ
  _/_ : ℕ -> ℕ -> ℕ

  set : Set -> Set
  singleton : forall {a} -> a -> set a
  toList : forall {a} -> set a -> List a

```
-->

* the length (in slots) of a voting round
  ```agda
  U : ℕ
  ```
* max. age for including vote certificate
  ```agda
  A : ℕ
  ```
* weight to cut off for common prefix
  ```agda
  W : ℕ
  ```
* the cutoff window (in slots) which is ignored to select block to vote for in a round
  ```agda
  L : ℕ
  ```
* weight boost per vote certificate
  ```agda
  B : ℕ
  ```
* number of votes required for quorum
  ```agda
  τ : ℕ
  ```
* chain-ignorance period
  ```agda
  R : ℕ
  ```
* the length of a cooldown period (in voting rounds)
  ```agda
  K : ℕ
  ```

Slot and round numbering

* The first slot (in which there can be a block) is 0; subsequent slots are numbered 1, 2 ,...
* Voting rounds are numbered 0, 1, 2, ..., and voting round $r$ corresponds to slots $rU$, $rU + 1$, $rU + 2$, ..., $(r+1)U - 1$. No votes are cast in round 0, which is successful by definition.

```agda
Slot = ℕ

Round = ℕ
```

The function `slot(.)` returns the slot number corresponding to the beginning of round a round, i.e., $slot(r) = r*T$.

```agda
slot : Round -> Slot
slot r = r / U
```

### Model

Chain/vote sync: each party is connected to a small number (e.g., 20) of upstream peers and downstream peers

### Blocks and Votes

<!--
```agda
postulate
  Party : Set
  Hash : Set
  Proof : Set
  Payload : Set
  Signature : Set
  Certificate : Set
```
-->

A Peras block consists of the following:

```agda
record Block : Set where
  constructor MkBlock
  field
   slot_number : Slot
   creator_ID : Party
   hash_of_parent_block : Hash
   certificate : Certificate
   slot-leadership_proof : Proof
   payload : Payload
   signature : Signature
```

For simplicity, the last three are ignored in the description of the protocol below.


A Peras vote consists of the following:

```agda
record Vote : Set where
 constructor MkVote
 field
  round_number : Round
  creator_ID : Party
  block_voted_for :  Block
```

A vote is valid if the committee-membership proof and the signature
are valid. For simplicity, however, those two are not made explicit in
the protocol description below. Also, the `block_voted_for` field is
described as a `Block` whereas, in practice, it would be a hash of the
block.

A Peras certificate represents an aggregated quorum of votes for a
specific block at a specific round. Such a certificate is supposed to
be self-contained and verifiable by any node.

<!--
```agda
postulate
```
-->

```agda
  Certify : Block -> Certificate -> Block
```

### Chains

A Peras chain consists of a set of blocks. A chain is valid if the blocks (ignoring the certificates) form a valid Praos chain.

```agda
postulate
  Chain : Set
  null : Certificate

  _isLeaderInSlot_ : Party -> Slot -> Bool
  _trimmedBy_ : Chain -> ℕ -> Chain
  _isCommitteeMemberInRound_ : Party -> Round -> Bool
  _pointsInto_ : Certificate -> Chain -> Bool

  length : Chain -> ℕ

  round : Certificate -> ℕ
```

The following algorithm is used to compute the weight, given a set of certificates:

```agda
chainWeight : Chain -> List Certificate -> ℕ
chainWeight chain certs =
   foldr (λ cert weight ->
           if (cert pointsInto chain)
           then weight + B
           else weight)
         (length chain) certs
```

In the following, $C[s]$ is a chain with all blocks newer than slot s removed.

```agda
postulate
  _⟦_⟧ : Chain -> Slot -> Block
```

## The Protocol

All code is described from the perspective of a single party $P$.

### Variables

<!--
```agda
postulate
```
-->

```agda
  Cpref : Chain                          -- Preferred Peras chain
  certseen : Certificate           -- Latest certificate in Certs
  certchain : Certificate         --  Latest certificate on Cpref
  Vpref : List (set Vote)     -- Pref. vote sets (idx’d by rd no)
  Certs : List Certificate -- Pref. certificates (idx’d by rd no)

```

Below, it is assumed that `certseen` and `certchain` are updated automatically when `Certs` or `Cpref` change.

<!--
```agda
data Node : Set -> Set₁ where
  bind : forall {a} {b} -> Node a -> (a -> Node b) -> Node b
  ret : forall {a} -> a -> Node a
  forgeBlock : Chain -> Node Block
  latestCertificateOnChain : Chain -> Node Certificate
  latestCertificateSeen : Node Certificate
  mkCertificate : Round -> Block -> Node Certificate
  existsBlockWithQuorum : set Vote -> (Maybe Block -> Node ⊤) -> Node ⊤
  _extendWith_ : Chain -> Block -> Node Chain
  output : Chain -> Node ⊤
  _:=_ : forall {a} -> a -> Node a -> Node ⊤
  _+=_ : forall {a : Set} -> a -> a -> Node ⊤

record Monad (M : Set -> Set₁) : Set where
  field
    _>>=_ : forall {a} {b} -> M a -> (a -> M b) -> M b
    return : forall {a} -> a -> M a

  _>>_ : forall {a} {b} -> M a -> M b -> M b
  m >> m' = m >>= λ _ -> m'

  when : forall {a} -> Bool -> M a -> M ⊤
  when cond act =
    if cond
     then act >> return _
     else return _

instance
  NodeMonad : Monad Node
  NodeMonad = record { _>>=_ = bind ; return = ret }

open Monad {{...}} public
```
-->

### Voting and Block Creation

Parties P vote and create blocks as follows:

```agda
onNewSlot : Party -> Slot -> Node ⊤
onNewSlot p s =
 when (p isLeaderInSlot s) (do
     b ← forgeBlock Cpref
     let rcurrent = s / U
     when
       ( (Certs [ rcurrent - 2 ]) == null
           ∧ ((rcurrent - round certseen) ≤ A)
           ∧ (round certseen > round certchain)
       ) do
         let b' = Certify b certseen
         Cpref ← Cpref extendWith b'
         output (Cpref trimmedBy W))
```

```agda
voteInRound : Chain -> List Certificate -> Round -> Bool
voteInRound chain certs r =
  (round certseen == (r - 1) ∧ certseen pointsInto Cpref)
   ∨ ((r - round certseen) ≥ R ∧ cooldownHasPassed (r - round certchain))
 where
    cooldownHasPassed : ℕ -> Bool
    cooldownHasPassed rounds with K
    ... | 0 = false
    ... | suc n = (q > 0) ∧ (r' == 0)
        where
         q = rounds div (suc n)
         r' = rounds % suc n

onNewRound : Party -> Round -> Node ⊤
onNewRound P r =
  when ( (P isCommitteeMemberInRound r) ∧
         voteInRound Cpref Certs r )
      ((Vpref [ r ]) += singleton (MkVote r P (Cpref ⟦ (slot r - L) ⟧)))
```

### Chain/Vote/Cert Sync

In Chain/Vote Sync, a party follows the preferred sets `(C’pref,
V’pref, Certs’pref)` of each of their upstream peers and makes their
own `(Cpref, Vpref, Certs)` available to all their downstream peers.

```agda
onPeerVotesChange : set Vote -> Round -> Node ⊤
onPeerVotesChange v'pref rcurrent = do
  when ((Certs [ rcurrent ]) == null) (do
     (Vpref [ rcurrent ]) += v'pref
     existsBlockWithQuorum (Vpref [ rcurrent ]) λ where
        nothing -> return _
        (just C) ->
          (Certs [ rcurrent ]) := mkCertificate rcurrent C
     )

onPeerCertsChange : Certificate -> Round -> Node ⊤
onPeerCertsChange certs'pref r =
  when ((Certs [ r ]) == null) $
     (Certs [ r ]) := return certs'pref

onPeerChainChange : Chain -> Certificate -> Node ⊤
onPeerChainChange C'pref Certs'pref = do
  when (chainWeight C'pref Certs > chainWeight Cpref Certs) $
     Cpref := return C'pref
  output (Cpref trimmedBy W)
```
