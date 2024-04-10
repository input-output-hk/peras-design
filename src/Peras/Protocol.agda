{-# OPTIONS --type-in-type --allow-unsolved-metas #-}
{- An attempt at "sideways-engineering" pseudo-code from Peras document -}
module Peras.Protocol where

open import Effect.Monad
open import Data.Nat hiding (_≟_ ; _>_ ; _/_)
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Data.Bool hiding (_≤_)
open import Data.Maybe using (Maybe ; nothing ; just)
open import Function using (_$_)

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

  _isLeaderInSlot_ : Party -> Slot -> Bool
  _trimmedBy_ : Chain -> ℕ -> Chain
  _isCommitteeMemberInRound_ : Party -> Round -> Bool

  round : Certificate -> ℕ

  _[_] : forall {a} -> List a -> ℕ -> a

  _⟦_⟧ : Chain -> Slot -> Chain

  _==_ : Certificate -> Certificate -> Bool

  _and_ : Bool -> Bool -> Bool
  _<=_ : ℕ -> ℕ -> Bool
  _>_ : ℕ -> ℕ -> Bool
  _-_ : ℕ -> ℕ -> ℕ
  _/_ : ℕ -> ℕ -> ℕ

  U : ℕ
  A : ℕ
  W : ℕ
  L : ℕ

data    Vote : Set where
 MkVote : Round -> Party -> Chain -> Vote


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
  _extendWith_ : Chain -> Block -> Node Chain
  output : Chain -> Node ⊤
  _:=_ : forall {a} -> a -> Node a -> Node ⊤
  _+=_ : forall {a} -> set a -> set a -> Node ⊤


existsBlockWithQuorum : set Vote -> (Maybe Block -> Node ⊤) -> Node ⊤
existsBlockWithQuorum = {!!}

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
     cpref ← preferredChain
     b ← forgeBlock cpref
     certs ← certificates
     certseen ← latestCertificateSeen
     certchain ← latestCertificateOnChain cpref
     let rcurrent = s / U
     when
       ( (certs [ rcurrent - 2 ]) == null
           ∧ ((rcurrent - round certseen) <= A)
           ∧ (round certseen > round certchain)
       ) do
         let b' = Certify b certseen
         cpref ← cpref extendWith b
         output (cpref trimmedBy W))

voteInRound : Chain -> List Certificate -> Round -> Bool
voteInRound = {!!}

-- upon entering new round r > 0
--   if P is committee member in round r and voteInRound(Cpref, Certs, r)
--     Vpref[r] += (“vote”, r, P, C[slot(r)-L])
onNewRound : Party -> Round -> Node ⊤
onNewRound P r = do
  cpref ← preferredChain
  certs ← certificates
  Vpref ← preferredVotes
  when ( (P isCommitteeMemberInRound r) ∧
         voteInRound cpref certs r )
      ((Vpref [ r ]) += singleton (MkVote r P (cpref ⟦ (slot r - L) ⟧)))

-- upon change in a peer’s V’pref[rcurrent]
--   if Certspref[rcurrent] = null
--      Vpref[rcurrent] += V’pref[rcurrent] 	preferring the versions in Vpref in case of equivocations
--      if exists C s.t. |{ (.,.,.,C) in Vpref[rcurrent] }| >= τ
--           create certificate cert on C from corresponding votes in Vpref[rcurrent]
--           Certspref[rcurrent] := cert

onPeerVotesChange : set Vote -> Round -> Node ⊤
onPeerVotesChange v'pref rcurrent = do
  certs ← certificates
  Vpref ← preferredVotes
  when ((certs [ rcurrent ]) == null) (do
     (Vpref [ rcurrent ]) += v'pref
     existsBlockWithQuorum (Vpref [ rcurrent ]) λ where
        nothing -> return _
        (just C) ->
          (certs [ rcurrent ]) := mkCertificate rcurrent C
     )


-- upon change in peer’s Certs’pref[r] for some r
--   if Certspref[r] = null
--     Certspref[r] := Certs’pref[r]

onPeerCertsChange : Certificate -> Round -> Node ⊤
onPeerCertsChange certs'pref r = do
  certspref ← certificates
  when ((certspref [ r ]) == null) $
     (certspref [ r ]) := return certs'pref
{-# COMPILE AGDA2HS onPeerCertsChange #-}


chainWeight : Chain -> List Certificate -> ℕ
chainWeight chain certs = {!!}

onPeerChainChange : Chain -> Certificate -> Node ⊤
onPeerChainChange C'pref Certs'pref = do
  cpref ← preferredChain
  certs ← certificates
  when (chainWeight C'pref certs > chainWeight cpref certs) $
     cpref := return C'pref
  output (cpref trimmedBy W)
