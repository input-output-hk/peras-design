
module Peras.Conformance.Model where

open import Haskell.Prelude
open import Haskell.Control.Monad
open import Agda.Builtin.Maybe hiding (Maybe)
open import Data.Nat using (ℕ; _/_; _%_; NonZero)
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
  {-# OPTIONS_GHC -Wno-name-shadowing -Wno-unused-matches #-}

  import Prelude hiding (round)
  import Control.Monad.Identity
  import Peras.Block (certificate, blockRef)
  import Peras.Crypto (hash)
  import Peras.Orphans ()
  import Data.Function (on)
  import qualified Data.Set as Set
  import Data.Set (Set)

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

{-# COMPILE AGDA2HS votingBlock #-}

vr1A : NodeModel → Bool
vr1A s = nextRound (round (cert' s)) == (rFromSlot s)

{-# COMPILE AGDA2HS vr1A #-}

vr1B : NodeModel → Block → Bool
vr1B s b = extends b (cert' s) (allChains s)

{-# COMPILE AGDA2HS vr1B #-}

vr2A : NodeModel → Bool
vr2A s = getRoundNumber (rFromSlot s) >= getRoundNumber (round (cert' s)) + perasR (protocol s)

{-# COMPILE AGDA2HS vr2A #-}

vr2B : NodeModel → Bool
vr2B s = (rFromSlot s) > round (certS s) && mod (getRoundNumber (rFromSlot s)) (perasK (protocol s)) == mod (getRoundNumber (round (certS s))) (perasK (protocol s))

{-# COMPILE AGDA2HS vr2B #-}

makeVote' : NodeModel → Maybe Vote
makeVote' s = do
  block ← votingBlock s
  guard (vr1A s && vr1B s block || vr2A s && vr2B s)
  pure $ makeVote (protocol s) (clock s) block

{-# COMPILE AGDA2HS makeVote' #-}

makeVote'' : NodeModel → Bool
makeVote'' s with votingBlock s
... | Just block = vr1A s && vr1B s block || vr2A s && vr2B s
... | Nothing = False

{-# COMPILE AGDA2HS makeVote'' #-}

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
  guard (makeVote'' s)
  Just ([] , record s { allVotes = v ∷ allVotes s })

{-# COMPILE AGDA2HS transition #-}
