module Peras.Conformance.Model where

open import Haskell.Prelude
open import Haskell.Prim
open import Haskell.Prim.Ord
open import Haskell.Control.Monad
open import Haskell.Extra.Dec
open import Haskell.Extra.Refinement
open import Haskell.Law.Equality using (cong)
open import Haskell.Law.Eq.Def
open import Haskell.Law.Eq.Instances
open import Haskell.Law.Ord.Def
open import Haskell.Law.Ord.Ordering

open import Data.Nat using (ℕ; _/_; _%_; NonZero; _≥_)

open import Peras.Block
open import Peras.Chain
open import Peras.Conformance.Params
open import Peras.Conformance.ProofPrelude using (eqBS-sound; not-eqBS-sound; any-prf)
open import Peras.Crypto
open import Peras.Foreign
open import Peras.Numbering
open import Peras.Util
import Protocol.Peras

{-# FOREIGN AGDA2HS
  {-# LANGUAGE RecordWildCards #-}
  {-# LANGUAGE NamedFieldPuns #-}
  {-# LANGUAGE TypeOperators #-}
  {-# OPTIONS_GHC -fno-warn-missing-pattern-synonym-signatures #-}
  {-# OPTIONS_GHC -fno-warn-missing-signatures #-}
  {-# OPTIONS_GHC -fno-warn-name-shadowing #-}
  {-# OPTIONS_GHC -fno-warn-type-defaults #-}
  {-# OPTIONS_GHC -fno-warn-unused-imports #-}
  {-# OPTIONS_GHC -fno-warn-unused-matches #-}

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

open Hashable

instance
  hashPayload : Hashable Payload
  hashPayload .hash = MkHash ∘ const emptyBS

  hashBlock : Hashable Block
  hashBlock .hash = MkHash ∘ bytesS ∘ signature

-- To avoid name clash for Vote.creatorId and Block.creatorId
voterId : Vote → PartyId
voterId (MkVote _ p _ _ _) = p

{-# COMPILE AGDA2HS voterId #-}

data EnvAction : Set where
  Tick     : EnvAction
  NewChain : Chain → EnvAction
  NewVote  : Vote → EnvAction
  BadChain : Chain → EnvAction
  BadVote  : Vote → EnvAction

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

otherId : PartyId
otherId = 2

{-# COMPILE AGDA2HS otherId #-}

seenBeforeStartOfRound : PerasParams → RoundNumber → Certificate × SlotNumber → Bool
seenBeforeStartOfRound params r (c , s) =
  getSlotNumber s <= getRoundNumber r * perasU params

{-# COMPILE AGDA2HS seenBeforeStartOfRound #-}

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
      party = mkParty sutId [] (r ∷ [])
      proof = createMembershipProof r (party ∷ [])
  in createSignedVote party r h proof 1

{-# COMPILE AGDA2HS makeVote #-}

-- The actual model ---

record NodeModel : Set where
  field
    clock        : SlotNumber
    protocol     : PerasParams
    allChains    : List Chain
    allVotes     : List Vote
    allSeenCerts : List Certificate

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
  in maximumBy genesisCert (comparing round) (mapMaybe certificate (pref s))

{-# COMPILE AGDA2HS certS #-}

open NodeModel public

{-# COMPILE AGDA2HS NodeModel deriving (Eq, Show) #-}

testParams : PerasParams
testParams =
  record defaultPerasParams
    { perasU = 5
    ; perasR = 1
    ; perasK = 1
    ; perasL = 1
    ; perasT = 0
    ; perasΔ = 0
    ; perasτ = 1
    }

{-# COMPILE AGDA2HS testParams #-}

initialModelState : NodeModel
initialModelState = record
  { clock            = 1
  ; protocol         = testParams
  ; allChains        = genesisChain ∷ []
  ; allVotes         = []
  ; allSeenCerts     = genesisCert ∷ []
  }

{-# COMPILE AGDA2HS initialModelState #-}

chainExtends : Hash Block → Certificate → Chain → Bool
chainExtends h c =
  any (λ block → Hashable.hash hashBlock block == blockRef c)
    ∘ dropWhile (λ block' → Hashable.hash hashBlock block' /= h)

{-# COMPILE AGDA2HS chainExtends #-}

extends : Hash Block → Certificate → List Chain → Bool
extends h cert chain =
  if cert == genesisCert
    then True
    else any (chainExtends h cert) chain

{-# COMPILE AGDA2HS extends #-}

private
  mod : ℕ → (n : ℕ) → @0 ⦃ NonZero n ⦄ → ℕ
  mod a b ⦃ prf ⦄ = _%_ a b ⦃ uneraseNonZero prf ⦄

votingBlockHash : NodeModel → Hash Block
votingBlockHash s =
  tipHash ∘ filter (λ {b → (getSlotNumber (slotNumber b)) + (perasL (protocol s)) <= (getSlotNumber (clock s))})
    $ pref s

{-# COMPILE AGDA2HS votingBlockHash #-}

addChain' : NodeModel → Chain → NodeModel
addChain' s c =
  record s
    { allChains = c ∷ (allChains s)
    ; allSeenCerts = foldr insertCert (allSeenCerts s) (mapMaybe certificate c)
    }

{-# COMPILE AGDA2HS addChain' #-}

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

certsFromQuorum : NodeModel → List Certificate
certsFromQuorum s = newQuora (fromNat (perasτ (protocol s))) (allSeenCerts s) (allVotes s)

{-# COMPILE AGDA2HS certsFromQuorum #-}

addVote' : NodeModel → Vote → NodeModel
addVote' s v =
  let s' = record s { allVotes = v ∷ (allVotes s) }
  in record s' { allSeenCerts = foldr insertCert (allSeenCerts s') (certsFromQuorum s') }

{-# COMPILE AGDA2HS addVote' #-}

hasVoted : PartyId → RoundNumber → NodeModel → Bool
hasVoted p r s = any (λ v → p == voterId v && r == votingRound v) (allVotes s)

{-# COMPILE AGDA2HS hasVoted #-}

instance
  iRoundNumber : IsLawfulEq RoundNumber
  iRoundNumber .isEquality (MkRoundNumber r₁) (MkRoundNumber r₂)
    with r₁ == r₂ in eq
  ... | True = cong MkRoundNumber (equality r₁ r₂ eq)
  ... | False = λ x → nequality r₁ r₂ eq (MkRoundNumber-inj x)
    where
      MkRoundNumber-inj : ∀ {x y} → MkRoundNumber x ≡ MkRoundNumber y → x ≡ y
      MkRoundNumber-inj refl = refl

_===_ : ∀ (x y : RoundNumber) → Dec (x ≡ y)
x === y = (x == y) ⟨ isEquality x y ⟩

{-# COMPILE AGDA2HS _===_ #-}

Vr1A : NodeModel → Set
Vr1A s = rFromSlot s ≡ nextRound (round (cert' s))

vr1A : (s : NodeModel) → Dec (Vr1A s)
vr1A s = rFromSlot s === nextRound (round (cert' s))

{-# COMPILE AGDA2HS vr1A #-}

Vr1B : NodeModel → Set
Vr1B s = Extends (votingBlockHash s) (cert' s) (allChains s)

vr1B' : NodeModel → Bool
vr1B' s = extends (votingBlockHash s) (cert' s) (allChains s)

{-# COMPILE AGDA2HS vr1B' #-}

eqBS-prf : ∀ (c : Certificate) → (x : Block) →
    Reflects
      (MkHash (bytesS (signature x)) ≡ blockRef c)
      (eqBS (bytesS (signature x)) (hashBytes (blockRef c)))
eqBS-prf c x =
  of
    {P = MkHash (bytesS (signature x)) ≡ blockRef c}
    {b = eqBS (bytesS (signature x)) (hashBytes (blockRef c))} ite
  where
    ite : if eqBS (bytesS (signature x)) (hashBytes (blockRef c))
          then (λ ⦃ @0 _ ⦄ → MkHash (bytesS (signature x)) ≡ blockRef c)
          else (λ ⦃ @0 _ ⦄ → MkHash (bytesS (signature x)) ≡ blockRef c → ⊥)
    ite
      with (MkHash (bytesS (signature x)) == blockRef c) in eq
    ite | True = cong MkHash (eqBS-sound eq)
    ite | False = not-eqBS-sound eq ∘ cong hashBytes

chainExtends-prf : (h : Hash Block) → (c : Certificate) → (ch : Chain)
  → Reflects (ChainExtends h c ch) (chainExtends h c ch)
chainExtends-prf h c ch = any-prf (dropWhile (λ b → Hashable.hash hashBlock b /= h) ch) (eqBS-prf c)

chainExtendsDec : (h : Hash Block) → (c : Certificate) → (ch : Chain) → Dec (ChainExtends h c ch)
chainExtendsDec h c ch = chainExtends h c ch ⟨ chainExtends-prf h c ch ⟩

extends-prf : (h : Hash Block) → (c : Certificate) → (ch : List Chain)
  → Reflects (Extends h c ch) (extends h c ch)
extends-prf h c ch =
  of
    {P = Extends h c ch}
    {b = extends h c ch} ite
  where
    ite : if extends h c ch
          then (λ ⦃ @0 _ ⦄ → Extends h c ch)
          else (λ ⦃ @0 _ ⦄ → Extends h c ch → ⊥)
    ite
      with c == genesisCert in eq
    ite | True = tt
    ite | False =
      let r = any-prf ch (chainExtends-prf h c)
      in invert {b = any (chainExtends h c) ch} r

extendsDec : (h : Hash Block) → (c : Certificate) → (ch : List Chain) → Dec (Extends h c ch)
extendsDec h c ch = extends h c ch ⟨ extends-prf h c ch ⟩

{-# COMPILE AGDA2HS extendsDec #-}

vr1B : (s : NodeModel) → Dec (Vr1B s)
vr1B s = extendsDec (votingBlockHash s) (cert' s) (allChains s)

{-# COMPILE AGDA2HS vr1B #-}

Vr2A : NodeModel → Set
Vr2A s =
    getRoundNumber (rFromSlot s)
  ≥ getRoundNumber (round (cert' s)) + perasR (protocol s)

vr2A : (s : NodeModel) → Dec (Vr2A s)
vr2A s =
  ge
    (getRoundNumber (rFromSlot s))
    (getRoundNumber (round (cert' s)) + perasR (protocol s))

{-# COMPILE AGDA2HS vr2A #-}

Vr2B : NodeModel → Set
Vr2B s =
  (getRoundNumber (rFromSlot s) Data.Nat.> getRoundNumber (round (certS s)))
    × ((mod (fromNat (getRoundNumber (rFromSlot s))) (fromNat (perasK (protocol s))))
       ≡ (mod (fromNat (getRoundNumber (round (certS s)))) (fromNat (perasK (protocol s)))))

vr2B : (s : NodeModel) → Dec (Vr2B s)
vr2B s = decP
  (gt
    (getRoundNumber (rFromSlot s))
    (getRoundNumber (round (certS s))))
  (eqDec (mod (fromNat (getRoundNumber (rFromSlot s))) (fromNat (perasK (protocol s))))
    (mod (fromNat (getRoundNumber (round (certS s)))) (fromNat (perasK (protocol s)))))

{-# COMPILE AGDA2HS vr2B #-}

CheckVotingRules : NodeModel → Set
CheckVotingRules s = Either (Vr1A s × Vr1B s) (Vr2A s × Vr2B s)

opaque
  checkVotingRules : (s : NodeModel) → Dec (CheckVotingRules s)
  checkVotingRules s =
    decS
      (decP (vr1A s) (vr1B s))
      (decP (vr2A s) (vr2B s))

{-# COMPILE AGDA2HS checkVotingRules #-}

checkVoteFromSut : Vote → Bool
checkVoteFromSut (MkVote _ c _ _ _) = c == sutId

{-# COMPILE AGDA2HS checkVoteFromSut #-}

checkVoteNotFromSut : Vote → Bool
checkVoteNotFromSut = not ∘ checkVoteFromSut

{-# COMPILE AGDA2HS checkVoteNotFromSut #-}

checkVoteFromOther : Vote → Bool
checkVoteFromOther (MkVote _ c _ _ _) = c == otherId

{-# COMPILE AGDA2HS checkVoteFromOther #-}

checkBlockFromSut : Block → Bool
checkBlockFromSut (MkBlock _ c _ _ _ _ _) = c == sutId

{-# COMPILE AGDA2HS checkBlockFromSut #-}

checkBlockNotFromSut : Block → Bool
checkBlockNotFromSut = not ∘ checkBlockFromSut

{-# COMPILE AGDA2HS checkBlockNotFromSut #-}

checkBlockFromOther : Block → Bool
checkBlockFromOther (MkBlock _ c _ _ _ _ _) = c == otherId

{-# COMPILE AGDA2HS checkBlockFromOther #-}

makeVote' : NodeModel → Maybe Vote
makeVote' s = do
  guard (isYes $ checkVotingRules s)
  guard (votingBlockHash s /= genesisHash)
  let v = makeVote (protocol s) (clock s) (votingBlockHash s)
  guard (slotToRound (protocol s) (clock s) == votingRound v)
  guard (checkVoteFromSut v)
  pure v

{-# COMPILE AGDA2HS makeVote' #-}

SutIsVoter = RoundNumber → Bool

{-# COMPILE AGDA2HS SutIsVoter #-}

voteInState : SutIsVoter → NodeModel → Maybe Vote
voteInState sutIsVoter s = do
  guard (sutIsVoter (rFromSlot s))
  guard (slotInRound (protocol s) (clock s) == 0)
  makeVote' s

{-# COMPILE AGDA2HS voteInState #-}

votesInState : SutIsVoter → NodeModel → List Vote
votesInState sutIsVoter = maybeToList ∘ voteInState sutIsVoter

{-# COMPILE AGDA2HS votesInState #-}

SutIsSlotLeader = SlotNumber → Bool

{-# COMPILE AGDA2HS SutIsSlotLeader #-}

chainInState : SutIsSlotLeader → NodeModel → Maybe Chain
chainInState sutIsSlotLeader s = do
  guard (sutIsSlotLeader (clock s))
  guard (slotNumber block == clock s)
  guard (checkBlockFromSut block)
  guard (parentBlock block == tipHash rest)
  guard (rest == pref s)
  guard (checkSignedBlock block)
  guard (checkLeadershipProof (leadershipProof block))
  guard (lastSlot rest < slotNumber block)
  guard (bodyHash block == Hashable.hash hashPayload [])
  pure (block ∷ rest)
  where
    rest = pref s
    notPenultimateCert : Certificate → Bool
    notPenultimateCert cert = getRoundNumber (round cert) + 2 /= getRoundNumber (rFromSlot s)
    noPenultimateCert = all notPenultimateCert (allSeenCerts s)
    unexpiredCert' = getRoundNumber (round (cert' s)) + perasA (protocol s) >= getRoundNumber (rFromSlot s)
    newerCert' = getRoundNumber (round (cert' s)) > getRoundNumber (round (certS s))
    includeCert' = noPenultimateCert && unexpiredCert' && newerCert'
    block = createSignedBlock
      (mkParty sutId [] [])
      (clock s)
      (tipHash rest)
      (if includeCert' then Just (cert' s) else Nothing)
      (createLeadershipProof (clock s) (mkParty sutId [] [] ∷ []))
      (MkHash emptyBS)

{-# COMPILE AGDA2HS chainInState #-}

chainsInState : SutIsSlotLeader → NodeModel → List Chain
chainsInState sutIsSlotLeader = maybeToList ∘ chainInState sutIsSlotLeader

{-# COMPILE AGDA2HS chainsInState #-}

transition : SutIsSlotLeader × SutIsVoter → NodeModel → EnvAction → Maybe ((List Chain × List Vote) × NodeModel)
transition (sutIsSlotLeader , sutIsVoter) s Tick =
  let s' = record s { clock = nextSlot (clock s) }
      votes = votesInState sutIsVoter  s'
      chains = chainsInState sutIsSlotLeader s'
  in
  Just ((chains , votes) ,
    let s'' = record s' { allVotes  = votes ++ allVotes s'
                        ; allChains = chains ++ allChains s'
                        }
    in record s'' { allSeenCerts = foldr insertCert (allSeenCerts s'') (certsFromQuorum s'') })
transition _ _ (NewChain []) = Nothing
transition _ s (NewChain (block ∷ rest)) = do
  guard (slotNumber block == clock s)
  guard (checkBlockFromOther block)
  guard (parentBlock block == tipHash rest)
  guard (rest == pref s)
  guard (checkSignedBlock block)
  guard (checkLeadershipProof (leadershipProof block))
  guard (lastSlot rest < slotNumber block)
  guard (bodyHash block == Hashable.hash hashPayload [])
  Just (([] , []) ,
    record s
      { allChains = (block ∷ rest) ∷ allChains s
      ; allSeenCerts = foldr insertCert (allSeenCerts s) (mapMaybe certificate (block ∷ rest))
      })
transition _ s (NewVote v) = do
  guard (slotInRound (protocol s) (clock s) == 0)
  guard (slotToRound (protocol s) (clock s) == votingRound v)
  guard (checkSignedVote v)
  guard (checkVoteFromOther v)
  -- checking voting rules for SUT as both parties have the same block-tree, see invariant
  guard (isYes $ checkVotingRules s)
  guard (votingBlockHash s == blockHash v)
  Just (([] , []) , addVote' s v)
transition _ s (BadChain blocks) = do
  guard (any (λ block → hasForged (slotNumber block) (creatorId block)) blocks)
  Just (([] , []) , s)
  where
    equivocatedBlock : SlotNumber → PartyId →  Block → Bool
    equivocatedBlock slot pid block = slot == slotNumber block && pid == creatorId block
    hasForged : SlotNumber → PartyId → Bool
    hasForged slot pid =
      any (any $ equivocatedBlock slot pid) $ allChains s
transition _ s (BadVote v) = do
  guard (hasVoted (voterId v) (votingRound v) s)
  Just (([] , []) , s)

{-# COMPILE AGDA2HS transition #-}
