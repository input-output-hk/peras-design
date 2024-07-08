
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
open import Data.Bool using ()
open import Data.Nat using (ℕ; _/_; _%_; NonZero; _≥_)
open import Data.Sum using (inj₁; inj₂; _⊎_; [_,_])

open import Peras.Block renaming (certificate to blockCert)
open import Peras.Chain
open import Peras.Conformance.Params
open import Peras.Crypto
open import Peras.Foreign
open import Peras.Numbering
open import Peras.SmallStep
open import Peras.Util
open import Protocol.Peras using ()

{-# FOREIGN AGDA2HS
  {-# LANGUAGE RecordWildCards #-}
  {-# LANGUAGE NamedFieldPuns #-}
  {-# LANGUAGE TypeOperators #-}
  {-# OPTIONS_GHC -Wno-name-shadowing -Wno-unused-matches #-}

  import Prelude hiding (round)
  import Control.Monad.Identity
  import Peras.Block (certificate, blockRef)
  import Peras.Crypto (hash)
  import Peras.Orphans ()
  import Data.Function (on)
  import qualified Data.Set as Set
  import Data.Set (Set)
  import GHC.Integer

  intToInteger :: Int -> Integer
  intToInteger = fromIntegral
#-}

-- Work around `agda2hs` limitations.

certificate : Block → Maybe Certificate
certificate record{certificate = just c}  = Just c
certificate record{certificate = nothing} = Nothing

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

makeVote : PerasParams → SlotNumber → Block → Vote
makeVote params slot block =
  let r = slotToRound params slot
      party = mkParty 1 [] (r ∷ [])
      proof = createMembershipProof r (party ∷ [])
  in createSignedVote party r (Hashable.hash hashBlock block) proof 1

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
  in maximumBy genesisCert (comparing round) (catMaybes (map certificate (pref s)))

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

{-# COMPILE AGDA2HS initialModelState #-}

blockOldEnough : PerasParams → SlotNumber → Block → Bool
blockOldEnough params clock record{slotNumber = slot} =
  getSlotNumber slot + perasL params + perasT params <= getSlotNumber clock

{-# COMPILE AGDA2HS blockOldEnough #-}

extends : Block → Certificate → List Chain → Bool
extends block cert chain =
  if cert == genesisCert
    then True
    else any chainExtends chain
    where
      chainExtends : Chain → Bool
      chainExtends =
        any (λ block → Hashable.hash hashBlock block == blockRef cert)
          ∘ dropWhile (λ block' → Hashable.hash hashBlock block' /= Hashable.hash hashBlock block)

{-# COMPILE AGDA2HS extends #-}

private
  mod : ℕ → (n : ℕ) → @0 ⦃ NonZero n ⦄ → ℕ
  mod a b ⦃ prf ⦄ = _%_ a b ⦃ uneraseNonZero prf ⦄

votingBlock : NodeModel → Maybe Block
votingBlock s = listToMaybe (dropWhile (not ∘ blockOldEnough (protocol s) (clock s)) (pref s))

postulate -- FIXME
  instance
    iRoundNumber : IsLawfulEq RoundNumber

{-# COMPILE AGDA2HS votingBlock #-}

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
    isYes≡True⇒value≡True {a = True ⟨ proof₁ ⟩} x = refl

@0 toWitness' : ∀ {A : Set} {a : Dec A} → TTrue a → A
toWitness' {a = True ⟨ prf ⟩} _ = prf

private
  variable
    A B : Set

_×-reflects_ : ∀ {a b} → Reflects A a → Reflects B b → Reflects (A × B) (a && b)
_×-reflects_ {A} {B} {True} {True} x y = x , y
_×-reflects_ {A} {B} {True} {False} _ y = λ { (_ , y₁) → y y₁ }
_×-reflects_ {A} {B} {False} {True} x _ = λ { (x₁ , _) → x x₁ }
_×-reflects_ {A} {B} {False} {False} x _ = λ { (x₁ , _) → x x₁ }

_⊎-reflects_ : ∀ {a b} → Reflects A a → Reflects B b → Reflects (A ⊎ B) (a || b)
_⊎-reflects_ {A} {B} {True} {True} x _ = inj₁ x
_⊎-reflects_ {A} {B} {True} {False} x _ = inj₁ x
_⊎-reflects_ {A} {B} {False} {True} _ y = inj₂ y
_⊎-reflects_ {A} {B} {False} {False} x y = [ x , y ]

decP : Dec A → Dec B → Dec (A × B)
decP (va ⟨ pa ⟩) (vb ⟨ pb ⟩) = (va && vb ) ⟨ pa ×-reflects pb ⟩

{-# COMPILE AGDA2HS decP #-}

decS : Dec A → Dec B → Dec (A ⊎ B)
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
Vr1B s = ⊤ -- FIXME

{-
with votingBlock s
... | Nothing = ⊥
... | Just block with extends block (cert' s) (allChains s)
... | True = ⊤
... | False = ⊥
-}

vr1B : (s : NodeModel) → Dec (Vr1B s)
vr1B s = True ⟨ tt ⟩

{-
vr1B : NodeModel → Bool
vr1B s =
  case votingBlock s of
    λ { (Just block) → extends block (cert' s) (allChains s)
      ; Nothing → False }
-}

{-# COMPILE AGDA2HS vr1B #-}

Vr2A : NodeModel → Set
Vr2A s = getRoundNumber (rFromSlot s) ≥ getRoundNumber (round (cert' s)) + perasR (protocol s)

vr2A : (s : NodeModel) → Dec (Vr2A s)
vr2A s = ge (getRoundNumber (rFromSlot s)) (getRoundNumber (round (cert' s)) + perasR (protocol s))

{-# COMPILE AGDA2HS vr2A #-}

Vr2B : NodeModel → Set
Vr2B s = ((getRoundNumber (rFromSlot s)) Data.Nat.> (getRoundNumber (round (certS s))))
       × ((mod (getRoundNumber (rFromSlot s)) (perasK (protocol s))) ≡ (mod (getRoundNumber (round (certS s))) (perasK (protocol s))))

vr2B : (s : NodeModel) → Dec (Vr2B s)
vr2B s = decP (gt (getRoundNumber (rFromSlot s)) (getRoundNumber (round (certS s))))
    (eq (mod (getRoundNumber (rFromSlot s)) (perasK (protocol s))) (mod (getRoundNumber (round (certS s))) (perasK (protocol s))))

{-# COMPILE AGDA2HS vr2B #-}

CheckVotingRules : NodeModel → Set
CheckVotingRules s = (Vr1A s × Vr1B s) ⊎ (Vr2A s × Vr2B s)

checkVotingRules : (s : NodeModel) → Dec (CheckVotingRules s)
checkVotingRules s = decS (decP (vr1A s) (vr1B s)) (decP (vr2A s) (vr2B s))

{-# COMPILE AGDA2HS checkVotingRules #-}

makeVote' : NodeModel → Maybe Vote
makeVote' s = do
  guard (isYes $ checkVotingRules s)
  block ← votingBlock s
  pure $ makeVote (protocol s) (clock s) block

{-# COMPILE AGDA2HS makeVote' #-}

votesInState : NodeModel → List Vote
votesInState s = maybeToList do
  guard (slotInRound params slot == 0)
  makeVote' s
  where
    params = protocol s
    slot   = clock s

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

transition : NodeModel → EnvAction → Maybe (List Vote × NodeModel)
transition s Tick =
  Just (sutVotes , record s' { allVotes = sutVotes ++ allVotes s'
                             ; allSeenCerts = foldr insertCert (allSeenCerts s') certsFromQuorum
                             })
  where s' = record s { clock = nextSlot (clock s) }
        sutVotes = votesInState s'
        certsFromQuorum = newQuora (fromNat (perasτ (protocol s))) (allSeenCerts s) (allVotes s)
transition s (NewChain chain) =
  Just ([] , record s
             { allChains = chain ∷ allChains s
             ; allSeenCerts = foldr insertCert (allSeenCerts s) (catMaybes $ map certificate chain)
             })
transition s (NewVote v) = do
  guard (slotInRound (protocol s) (clock s) == 0)
  guard (checkSignedVote v)
  guard (isYes $ checkVotingRules s)
  Just ([] , record s { allVotes = v ∷ allVotes s })

{-# COMPILE AGDA2HS transition #-}
