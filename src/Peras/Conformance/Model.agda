module Peras.Conformance.Model where

open import Haskell.Prelude
open import Haskell.Control.Monad
open import Haskell.Extra.Dec
open import Haskell.Extra.Refinement
open import Haskell.Law.Equality using (cong)
open import Haskell.Law.Eq.Def
open import Haskell.Law.Eq.Instances
open import Haskell.Law.Ord.Def

open import Agda.Builtin.Maybe hiding (Maybe)
import Data.Bool
import Data.List
open import Data.Nat using (ℕ; _/_; _%_; NonZero; _≥_)
open import Data.Sum using (inj₁; inj₂; _⊎_; [_,_])
import Data.Product as P

open import Peras.Block
open import Peras.Chain
open import Peras.Conformance.Params
open import Peras.Crypto
open import Peras.Foreign
open import Peras.Numbering
open import Peras.Util
import Protocol.Peras

{-# FOREIGN AGDA2HS
  {-# LANGUAGE RecordWildCards #-}
  {-# LANGUAGE NamedFieldPuns #-}
  {-# LANGUAGE TypeOperators #-}
  {-# OPTIONS_GHC -Wno-name-shadowing -Wno-unused-matches #-}

  import Prelude hiding (round)
  import Control.Monad.Identity
  import Peras.Crypto (hash)
  import Peras.Orphans ()
  import Data.Function (on)
  import qualified Data.Set as Set
  import Data.Set (Set)
  import GHC.Integer

  intToInteger :: Int -> Integer
  intToInteger = fromIntegral
#-}

data EnvAction : Set where
  Tick     : EnvAction
  NewChain : Chain → EnvAction
  NewVote  : Vote → EnvAction

{-# COMPILE AGDA2HS EnvAction deriving (Eq, Show) #-}

genesisHash : Hash Block
genesisHash = MkHash emptyBS

{-# COMPILE AGDA2HS genesisHash #-}

genesisChain : Chain
genesisChain = []

{-# COMPILE AGDA2HS genesisChain #-}

genesisCert : Certificate
genesisCert = MkCertificate 0 genesisHash

{-# COMPILE AGDA2HS genesisCert #-}

sutId : PartyId
sutId = 1

{-# COMPILE AGDA2HS sutId #-}

insertCert : Certificate → List Certificate → List Certificate
insertCert cert [] = cert ∷ []
insertCert cert (cert' ∷ certs) =
  if cert == cert'
  then cert' ∷ certs
  else cert' ∷ insertCert cert certs

{-# COMPILE AGDA2HS insertCert #-}

seenBeforeStartOfRound : PerasParams → RoundNumber → Certificate × SlotNumber → Bool
seenBeforeStartOfRound params r (c , s) =
  getSlotNumber s <= getRoundNumber r * perasU params

{-# COMPILE AGDA2HS seenBeforeStartOfRound #-}

-- FIXME: Relocate this.
instance
    hashBlock : Hashable Block
    hashBlock = record
      { hash = λ b →
               (let record { bytesS = s } = signature b
                  in record { hashBytes = s })
      }

chainWeight : Nat → List Certificate -> Chain → Nat
chainWeight boost certs = chainWeight' 0
  where
    isCertified : Block → Bool
    isCertified block = any (λ cert → Hashable.hash hashBlock block == blockRef cert) certs
    chainWeight' : Nat → List Block → Nat
    chainWeight' accum [] = accum
    chainWeight' accum (block ∷ blocks) =
      if isCertified block
        then chainWeight' (accum + 1 + boost) blocks
        else chainWeight' (accum + 1) blocks

{-# COMPILE AGDA2HS chainWeight #-}

compareTip : Chain → Chain → Ordering
compareTip [] [] = EQ
compareTip [] _ = LT
compareTip _ [] = GT
compareTip (block1 ∷ blocks1) (block2 ∷ blocks2) =
  case compare (slotNumber block1) (slotNumber block2) of λ where
    EQ → case compare (creatorId block1) (creatorId block2) of λ where
      EQ → compare (signature block1) (signature block2)
      y → y
    x → x

{-# COMPILE AGDA2HS compareTip #-}

compareChains : Nat → List Certificate → Chain → Chain → Ordering
compareChains boost certs chain1 chain2 =
  case compare (chainWeight boost certs chain1) (chainWeight boost certs chain2) of λ where
    EQ → compareTip chain1 chain2
    x → x

{-# COMPILE AGDA2HS compareChains #-}

preferredChain : PerasParams → List Certificate → List Chain → Chain
preferredChain params certs =
  maximumBy genesisChain (compareChains (fromNat (perasB params)) certs)

{-# COMPILE AGDA2HS preferredChain #-}

makeVote : PerasParams → SlotNumber → Hash Block → Vote
makeVote params slot h =
  let r = slotToRound params slot
      party = mkParty 1 [] (r ∷ [])
      proof = createMembershipProof r (party ∷ [])
  in createSignedVote party r h proof 1

{-# COMPILE AGDA2HS makeVote #-}

-- The actual model ---

record NodeModel : Set where
  field
    clock            : SlotNumber
    protocol         : PerasParams
    allChains        : List Chain
    allVotes         : List Vote
    allSeenCerts     : List Certificate

rFromSlot : NodeModel → RoundNumber
rFromSlot s =
  let open NodeModel s
  in slotToRound protocol clock

{-# COMPILE AGDA2HS rFromSlot #-}

cert' : NodeModel → Certificate
cert' s =
  let open NodeModel s
  in maximumBy genesisCert (comparing round) allSeenCerts

{-# COMPILE AGDA2HS cert' #-}

pref : NodeModel → Chain
pref s =
  let open NodeModel s
  in preferredChain protocol allSeenCerts allChains

{-# COMPILE AGDA2HS pref #-}

certS : NodeModel → Certificate
certS s =
  let open NodeModel s
  in maximumBy genesisCert (comparing round) (Data.List.mapMaybe certificate (pref s))

{-# COMPILE AGDA2HS certS #-}

open NodeModel public

{-# COMPILE AGDA2HS NodeModel deriving (Eq, Show) #-}

initialModelState : NodeModel
initialModelState = record
  { clock            = 1
  ; protocol         = record defaultPerasParams
                       { perasU = 5
                       ; perasR = 1
                       ; perasK = 1
                       ; perasL = 1
                       ; perasT = 0
                       ; perasΔ = 0
                       ; perasτ = 1
                       }
  ; allChains        = genesisChain ∷ []
  ; allVotes         = []
  ; allSeenCerts     = genesisCert ∷ []
  }

initialModelState' : PerasParams → NodeModel
initialModelState' params = record
  { clock            = 1
  ; protocol         = params
  ; allChains        = genesisChain ∷ []
  ; allVotes         = []
  ; allSeenCerts     = genesisCert ∷ []
  }

{-# COMPILE AGDA2HS initialModelState #-}

blockOldEnough : PerasParams → SlotNumber → Block → Bool
blockOldEnough params clock record{slotNumber = slot} =
  getSlotNumber slot + perasL params + perasT params <= getSlotNumber clock

{-# COMPILE AGDA2HS blockOldEnough #-}

chainExtends : Hash Block → Certificate → Chain → Bool
chainExtends h c =
  any (λ block → Hashable.hash hashBlock block == blockRef c)
    ∘ dropWhile (λ block' → Hashable.hash hashBlock block' /= h)

{-# COMPILE AGDA2HS chainExtends #-}

extends : Hash Block → Certificate → List Chain → Bool
extends h cert = any (chainExtends h cert)

{-# COMPILE AGDA2HS extends #-}

private
  mod : ℕ → (n : ℕ) → @0 ⦃ NonZero n ⦄ → ℕ
  mod a b ⦃ prf ⦄ = _%_ a b ⦃ uneraseNonZero prf ⦄

opaque
  votingBlockHash : NodeModel → Hash Block
  votingBlockHash s = hashHead ∘ filter (λ {b → (getSlotNumber (slotNumber b)) + (perasL (protocol s)) <= (getSlotNumber (clock s))}) $ pref s

{-# COMPILE AGDA2HS votingBlockHash #-}

newChain' : NodeModel → Chain → NodeModel
newChain' s c = record s { allChains = c ∷ (allChains s) }

{-# COMPILE AGDA2HS newChain' #-}

addVote' : NodeModel → Vote → NodeModel
addVote' s v = record s { allVotes = v ∷ (allVotes s) }

{-# COMPILE AGDA2HS addVote' #-}

open import Peras.Params
open Hashable

module TreeInstance
         ⦃ _ : Hashable (List Tx) ⦄
         ⦃ _ : Params ⦄
         ⦃ _ : Network ⦄
         ⦃ _ : Postulates ⦄
       where

{-
  valid-NodeModel : ∀ (m : NodeModel) → ValidChain (pref m)
  valid-NodeModel m with pref m
  ... | [] = Genesis
  ... | x ∷ xxx = Cons {!!} {!!} {!!} {!!} {!!}
-}

  open import Peras.SmallStep using (TreeType; IsTreeType)

  postulate
    isTreeType : IsTreeType initialModelState newChain' allChains pref addVote' allVotes allSeenCerts genesisCert
    isTreeType' : (params : PerasParams) → IsTreeType (initialModelState' params) newChain' allChains pref addVote' allVotes allSeenCerts genesisCert

{-
  isTreeType = record
                 { instantiated = refl
                 ; instantiated-certs = refl
                 ; instantiated-votes = refl
                 ; extendable-chain = {!!}
                 ; valid = valid-NodeModel
                 ; optimal = {!!}
                 ; self-contained = {!!}
                 ; valid-votes = {!!}
                 ; unique-votes = {!!}
                 ; no-equivocations = {!!}
                 ; quorum-cert = {!!}
                 }
-}

  NodeModelTree : TreeType NodeModel
  NodeModelTree = record {
    tree₀ = initialModelState ;
    allChains = allChains ;
    votes = allVotes ;
    certs = allSeenCerts ;
    newChain = newChain' ;
    preferredChain = pref;
    addVote = addVote' ;
    is-TreeType = isTreeType
    }

  NodeModelTree' : PerasParams → TreeType NodeModel
  NodeModelTree' params = record {
    tree₀ = initialModelState' params ;
    allChains = allChains ;
    votes = allVotes ;
    certs = allSeenCerts ;
    newChain = newChain' ;
    preferredChain = pref;
    addVote = addVote' ;
    is-TreeType = isTreeType' params
    }

postulate -- FIXME
  instance
    iRoundNumber : IsLawfulEq RoundNumber

isYes : ∀ {A : Set} → Dec A → Bool
isYes (True ⟨ _ ⟩) = True
isYes (False ⟨ _ ⟩) = False

{-# COMPILE AGDA2HS isYes #-}

TTrue : ∀ {A : Set} → Dec A → Set
TTrue a = Data.Bool.T (isYes a)

toTT : ∀ {A : Set} → {a : Dec A} → value a ≡ True → TTrue {A} a
toTT refl = tt

@0 isYes≡True⇒TTrue : ∀ {A : Set} → {a : Dec A} → isYes a ≡ True → TTrue {A} a
isYes≡True⇒TTrue x = toTT (isYes≡True⇒value≡True x)
  where
    isYes≡True⇒value≡True : ∀ {A : Set} → {a : Dec A} → isYes a ≡ True → value a ≡ True
    isYes≡True⇒value≡True {a = True ⟨ _ ⟩} _ = refl

@0 toWitness : ∀ {A : Set} {a : Dec A} → TTrue a → A
toWitness {a = True ⟨ prf ⟩} _ = prf

_×-reflects_ : ∀ {a b} {A B : Set} → Reflects A a → Reflects B b → Reflects (A P.× B) (a && b)
_×-reflects_ {True} {True} x y = x P., y
_×-reflects_ {True} {False} _ y = λ { (_ P., y₁) → y y₁ }
_×-reflects_ {False} {True} x _ = λ { (x₁ P., _) → x x₁ }
_×-reflects_ {False} {False} x _ = λ { (x₁ P., _) → x x₁ }

_⊎-reflects_ : ∀ {a b} {A B : Set} → Reflects A a → Reflects B b → Reflects (A ⊎ B) (a || b)
_⊎-reflects_ {True} {True} x _ = inj₁ x
_⊎-reflects_ {True} {False} x _ = inj₁ x
_⊎-reflects_ {False} {True} _ y = inj₂ y
_⊎-reflects_ {False} {False} x y = [ x , y ]

decP : ∀ {A B : Set} → Dec A → Dec B → Dec (A P.× B)
decP (va ⟨ pa ⟩) (vb ⟨ pb ⟩) = (va && vb ) ⟨ pa ×-reflects pb ⟩

{-# COMPILE AGDA2HS decP #-}

decS : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
decS (va ⟨ pa ⟩) (vb ⟨ pb ⟩) = (va || vb ) ⟨ pa ⊎-reflects pb ⟩

{-# COMPILE AGDA2HS decS #-}

_===_ : ∀ (x y : RoundNumber) → Dec (x ≡ y)
x === y = (x == y) ⟨ isEquality x y ⟩

{-# COMPILE AGDA2HS _===_ #-}

postulate
  eq : ∀ (x y : ℕ) → Dec (x ≡ y)
  ge : ∀ x y → Dec (x ≥ y)
  gt : ∀ x y → Dec (x Data.Nat.> y)

{-# FOREIGN AGDA2HS
  eq :: Integer -> Integer -> Bool
  eq = (==)

  gt :: Integer -> Integer -> Bool
  gt = gtInteger

  ge :: Integer -> Integer -> Bool
  ge = geInteger
#-}

Vr1A : NodeModel → Set
Vr1A s = nextRound (round (cert' s)) ≡ rFromSlot s

vr1A : (s : NodeModel) → Dec (Vr1A s)
vr1A s = nextRound (round (cert' s)) === rFromSlot s

{-# COMPILE AGDA2HS vr1A #-}

Vr1B : NodeModel → Set
Vr1B s = Extends (votingBlockHash s) (cert' s) (allChains s)

vr1B' : NodeModel → Bool
vr1B' s = extends (votingBlockHash s) (cert' s) (allChains s)

{-# COMPILE AGDA2HS vr1B' #-}

postulate
  vr1B-prf : ∀ {s} → Reflects (Vr1B s) (vr1B' s)

vr1B : (s : NodeModel) → Dec (Vr1B s)
vr1B s = vr1B' s ⟨ vr1B-prf {s} ⟩

{-# COMPILE AGDA2HS vr1B #-}

Vr2A : NodeModel → Set
Vr2A s = getRoundNumber (rFromSlot s) ≥ getRoundNumber (round (cert' s)) + perasR (protocol s)

vr2A : (s : NodeModel) → Dec (Vr2A s)
vr2A s = ge (getRoundNumber (rFromSlot s)) (getRoundNumber (round (cert' s)) + perasR (protocol s))

{-# COMPILE AGDA2HS vr2A #-}

Vr2B : NodeModel → Set
Vr2B s = ((getRoundNumber (rFromSlot s)) Data.Nat.> (getRoundNumber (round (certS s))))
    P.× ((mod (getRoundNumber (rFromSlot s)) (perasK (protocol s))) ≡ (mod (getRoundNumber (round (certS s))) (perasK (protocol s))))

vr2B : (s : NodeModel) → Dec (Vr2B s)
vr2B s = decP (gt (getRoundNumber (rFromSlot s)) (getRoundNumber (round (certS s))))
    (eq (mod (getRoundNumber (rFromSlot s)) (perasK (protocol s))) (mod (getRoundNumber (round (certS s))) (perasK (protocol s))))

{-# COMPILE AGDA2HS vr2B #-}

CheckVotingRules : NodeModel → Set
CheckVotingRules s = (Vr1A s P.× Vr1B s) ⊎ (Vr2A s P.× Vr2B s)

opaque
  checkVotingRules : (s : NodeModel) → Dec (CheckVotingRules s)
  checkVotingRules s =
    decS
      (decP (vr1A s) (vr1B s))
      (decP (vr2A s) (vr2B s))

{-# COMPILE AGDA2HS checkVotingRules #-}

makeVote' : NodeModel → Maybe Vote
makeVote' s = do
  guard (isYes $ checkVotingRules s)
  guard (votingBlockHash s /= genesisHash)
  pure $ makeVote (protocol s) (clock s) (votingBlockHash s)

{-# COMPILE AGDA2HS makeVote' #-}

votesInState : NodeModel → List Vote
votesInState s = maybeToList do
  guard (slotInRound (protocol s) (clock s) == 0)
  makeVote' s

{-# COMPILE AGDA2HS votesInState #-}

{-# TERMINATING #-}
newQuora : ℕ → List Certificate → List Vote → List Certificate
newQuora _ _ [] = []
newQuora quorum priorCerts (vote ∷ votes) =
  let
    sameCert cert = votingRound vote == round cert && blockHash vote == blockRef cert
    sameVote vote' = votingRound vote == votingRound vote' && blockHash vote == blockHash vote'
    hasCertificate = any sameCert priorCerts
    voteCount = length (filter sameVote votes) + 1
    hasQuorum = intToInteger voteCount >= fromNat quorum
    remainder = filter (not ∘ sameVote) votes
  in
    if not hasCertificate && hasQuorum
      then (
        let newCert = MkCertificate (votingRound vote) (blockHash vote)
        in newCert ∷ newQuora quorum (newCert ∷ priorCerts) remainder
      )
      else newQuora quorum priorCerts remainder

{-# COMPILE AGDA2HS newQuora #-}

checkVoteFromSut : Vote → Bool
checkVoteFromSut (MkVote _ c _ _ _) = c == sutId

{-# COMPILE AGDA2HS checkVoteFromSut #-}

opaque
  checkVoteNotFromSut : Vote → Bool
  checkVoteNotFromSut = not ∘ checkVoteFromSut

{-# COMPILE AGDA2HS checkVoteNotFromSut #-}

checkBlockFromSut : Block → Bool
checkBlockFromSut (MkBlock _ c _ _ _ _ _) = c == sutId

{-# COMPILE AGDA2HS checkBlockFromSut #-}

checkBlockNotFromSut : Block → Bool
checkBlockNotFromSut = not ∘ checkBlockFromSut

{-# COMPILE AGDA2HS checkBlockNotFromSut #-}

transition : NodeModel → EnvAction → Maybe (List Vote × NodeModel)
transition s Tick =
  Just (sutVotes , record s' { allVotes = sutVotes ++ allVotes s'
                             ; allSeenCerts = foldr insertCert (allSeenCerts s') certsFromQuorum
                             })
  where s' = record s { clock = nextSlot (clock s) }
        sutVotes = votesInState s'
        certsFromQuorum = newQuora (fromNat (perasτ (protocol s))) (allSeenCerts s) (allVotes s)
transition s (NewChain chain) = do
--  guard (length chain > 0) -- TODO: use NonEmpty
--  guard (checkBlockNotFromSut (head chain))
  Just ([] , record s
             { allChains = chain ∷ allChains s
             ; allSeenCerts = foldr insertCert (allSeenCerts s) (Data.List.mapMaybe certificate chain)
             })
transition s (NewVote v) = do
  guard (slotInRound (protocol s) (clock s) == 0)
  guard (checkSignedVote v)
  guard (checkVoteNotFromSut v)
  -- TODO: do we know that the voting rules have been checked
  --       by the vote creator? We don't have all the block-trees in
  --       the test model. The following should use the block-tree of
  --       the vote creator for checking the voting rules:
  guard (isYes $ checkVotingRules s)
  guard (votingBlockHash s == blockHash v)
  Just ([] , addVote' s v)

{-# COMPILE AGDA2HS transition #-}
