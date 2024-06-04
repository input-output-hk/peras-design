{-# OPTIONS --type-in-type --allow-unsolved-metas #-}
{- An attempt at "sideways-engineering" pseudo-code from Peras document -}
module Protocol.Peras where

open import Effect.Monad
open import Data.Nat.DivMod using ( _div_ ; _mod_ )
open import Data.Nat hiding (_≟_ ; _>_ ; _/_ ; _≤_ ; _≥_ )
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Data.List using (foldr ; map)
open import Data.Bool hiding (_≤_)
open import Data.Maybe using (Maybe ; nothing ; just)
open import Function using (_$_)

{-
Preliminaries
Parameters
Ouroboros Peras has the following parameters:
T: the length (in slots) of a voting round
K: the length of a cooldown period (in voting rounds)
R: chain-ignorance period
L: the cutoff window (in slots) which is ignored to select block to vote for in a round
Llow, Lhigh: define vote-candidate window
A: max. age for including vote certificate
τ: number of votes required for quorum
b B: weight boost per vote certificate
W: weight to cut off for common prefix
-}

Slot = ℕ

Round = ℕ

postulate
  Party : Set
  Chain : Set
  Block : Set
  Certificate : Set
  Certify : Block -> Certificate -> Block

  set : Set -> Set
  singleton : forall {a} -> a -> set a
  null : Certificate
  toList : forall {a} -> set a -> List a

  _isLeaderInSlot_ : Party -> Slot -> Bool
  _trimmedBy_ : Chain -> ℕ -> Chain
  _isCommitteeMemberInRound_ : Party -> Round -> Bool
  _pointsInto_ : Certificate -> Chain -> Bool

  length : Chain -> ℕ

  round : Certificate -> ℕ

  _[_] : forall {a} -> List a -> ℕ -> a

  _⟦_⟧ : Chain -> Slot -> Block

  _==_ : forall {a : Set} -> a -> a -> Bool

  _and_ : Bool -> Bool -> Bool
  _≤_ : ℕ -> ℕ -> Bool
  _≥_ : ℕ -> ℕ -> Bool
  _>_ : ℕ -> ℕ -> Bool
  _-_ : ℕ -> ℕ -> ℕ
  _/_ : ℕ -> ℕ -> ℕ

  U : ℕ
  A : ℕ
  W : ℕ
  L : ℕ
  B : ℕ
  R : ℕ
  K : ℕ

data Vote : Set where
 MkVote : Round -> Party -> Block -> Vote

slot : Round -> Slot
slot r = r / U

infixl 4 _-_
infixl 10 _[_]

data Node : Set -> Set₁ where
  bind : forall {a} {b} -> Node a -> (a -> Node b) -> Node b
  ret : forall {a} -> a -> Node a
  forgeBlock : Chain -> Node Block
  preferredChain : Node Chain
  preferredVotes : Node (List (set Vote))
  certificates : Node (List Certificate)
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

postulate
  Cpref : Chain
  certseen : Certificate
  certchain : Certificate
  Vpref : List (set Vote)
  Certs : List Certificate

-- Original specification from Google doc
--
-- upon entering new slot s
--    if P is leader in slot s
--      B := new block extending Cpref
--      if Certs[rcurrent-2] = null
--         and rcurrent - round(certseen) <= A
--         and round(certseen) > round(certchain)
--           B := (B, certseen)
--           Cpref := Cpref || B
--           output (chain, Cpref<-W>) to Z
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
         Cpref ← Cpref extendWith b
         output (Cpref trimmedBy W))

-- if (round(certseen) = r-1 and certseen is for a block on Cpref)
--    or
--    r - round(certseen) >= R and r - round(certchain) = cK for some c > 0
--   return true
-- return false

cooldownHasPassed : ℕ -> Bool
cooldownHasPassed rounds with K
... | 0 = false
... | suc n = (q > 0) ∧ (r == 0)
    where
     q = rounds div (suc n)
     r = rounds % suc n

voteInRound : Chain -> List Certificate -> Round -> Bool
voteInRound chain certs r =
  (round certseen == (r - 1) ∧ certseen pointsInto Cpref)
   ∨ ((r - round certseen) ≥ R ∧ cooldownHasPassed (r - round certchain))


-- upon entering new round r > 0
--   if P is committee member in round r and voteInRound(Cpref, Certs, r)
--     Vpref[r] += (“vote”, r, P, C[slot(r)-L])
onNewRound : Party -> Round -> Node ⊤
onNewRound P r =
  when ( (P isCommitteeMemberInRound r) ∧
         voteInRound Cpref Certs r )
      ((Vpref [ r ]) += singleton (MkVote r P (Cpref ⟦ (slot r - L) ⟧)))

-- upon change in a peer’s V’pref[rcurrent]
--   if Certspref[rcurrent] = null
--      Vpref[rcurrent] += V’pref[rcurrent] 	preferring the versions in Vpref in case of equivocations
--      if exists C s.t. |{ (.,.,.,C) in Vpref[rcurrent] }| >= τ
--           create certificate cert on C from corresponding votes in Vpref[rcurrent]
--           Certspref[rcurrent] := cert

onPeerVotesChange : set Vote -> Round -> Node ⊤
onPeerVotesChange v'pref rcurrent = do
  when ((Certs [ rcurrent ]) == null) (do
     (Vpref [ rcurrent ]) += v'pref
     existsBlockWithQuorum (Vpref [ rcurrent ]) λ where
        nothing -> return _
        (just C) ->
          (Certs [ rcurrent ]) := mkCertificate rcurrent C
     )


-- upon change in peer’s Certs’pref[r] for some r
--   if Certspref[r] = null
--     Certspref[r] := Certs’pref[r]

onPeerCertsChange : Certificate -> Round -> Node ⊤
onPeerCertsChange certs'pref r =
  when ((Certs [ r ]) == null) $
     (Certs [ r ]) := return certs'pref

-- A Peras chain consists of a set of blocks. A chain is valid if the blocks (ignoring the certificates) form a valid Praos chain.
-- The following algorithm is used to compute the weight, given a set of certificates:

chainWeight : Chain -> List Certificate -> ℕ
chainWeight chain certs =
   foldr (λ cert weight ->
           if (cert pointsInto chain)
           then  weight + B
           else weight)
         (length chain) certs

onPeerChainChange : Chain -> Certificate -> Node ⊤
onPeerChainChange C'pref Certs'pref = do
  when (chainWeight C'pref Certs > chainWeight Cpref Certs) $
     Cpref := return C'pref
  output (Cpref trimmedBy W)
