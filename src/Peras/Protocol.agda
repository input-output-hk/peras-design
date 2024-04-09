{-# OPTIONS --type-in-type #-}
{- An attempt at "sideways-engineering" pseudo-code from Peras document -}
module Peras.Protocol where

open import Effect.Monad
open import Data.Nat hiding (_≟_ ; _>_ ; _/_)
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Data.Bool hiding (_≤_)

Slot = ℕ

postulate
  Party : Set
  Chain : Set
  Block : Set
  Certificate : Set
  Certify : Block -> Certificate -> Block

  null : Certificate

  isLeaderInSlot : Party -> Slot -> Bool
  _trimmedBy_ : Chain -> ℕ -> Chain

  round : Certificate -> ℕ

  _[_] : List Certificate -> ℕ -> Certificate

  _==_ : Certificate -> Certificate -> Bool

  _and_ : Bool -> Bool -> Bool
  _<=_ : ℕ -> ℕ -> Bool
  _>_ : ℕ -> ℕ -> Bool
  _-_ : ℕ -> ℕ -> ℕ
  _/_ : ℕ -> ℕ -> ℕ

  U : ℕ
  A : ℕ
  W : ℕ


data Node : Set -> Set₁ where
  bind : forall {a} {b} -> Node a -> (a -> Node b) -> Node b
  ret : forall {a} -> a -> Node a
  forgeBlock : Chain -> Node Block
  preferredChain : Node Chain
  certificates : Node (List Certificate)
  latestCertificateOnChain : Chain -> Node Certificate
  latestCertificateSeen : Node Certificate
  _extendWith_ : Chain -> Block -> Node Chain
  output : Chain -> Node ⊤
  _:=_ : forall {a} -> a -> Node a -> Node ⊤

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

onNewSlot : Party -> Slot -> Node ⊤
onNewSlot p s =
 when (isLeaderInSlot p s) (do
     cpref <- preferredChain
     b <- forgeBlock cpref
     certs <- certificates
     certseen <- latestCertificateSeen
     certchain <- latestCertificateOnChain cpref
     let rcurrent = s / U
     when
       ( ((certs [ (rcurrent - 2) ]) == null)
           ∧ ((rcurrent - round certseen) <= A)
           ∧ (round certseen > round certchain)
       ) do
         let b' = Certify b certseen
         cpref <- cpref extendWith b
         output (cpref trimmedBy W))
