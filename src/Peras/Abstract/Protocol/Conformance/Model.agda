
module Peras.Abstract.Protocol.Conformance.Model where

open import Haskell.Prelude
open import Haskell.Control.Monad
open import Agda.Builtin.Maybe hiding (Maybe)
open import Data.Nat using (ℕ; _/_; _%_; NonZero)
open import Peras.SmallStep
open import Peras.Block renaming (certificate to blockCert)
open import Peras.Chain
open import Peras.Crypto
open import Peras.Numbering
open import Peras.Util
open import Peras.Abstract.Protocol.Params
open import Protocol.Peras using ()

{-# FOREIGN AGDA2HS
  {-# LANGUAGE RecordWildCards #-}
  {-# LANGUAGE NamedFieldPuns #-}
  {-# OPTIONS_GHC -Wno-name-shadowing -Wno-unused-matches #-}
#-}

{-# FOREIGN AGDA2HS
  import Prelude hiding (round)
  import Control.Monad.Identity
  import Peras.Block (certificate, blockRef)
  import Peras.Crypto (hash)
  import Data.Function (on)
  import qualified Data.Set as Set
  import Data.Set (Set)
  import Peras.Abstract.Protocol.Crypto (mkCommitteeMember, createMembershipProof, createSignedVote, mkParty, createSignedCertificate)
  intToInteger :: Int -> Integer
  intToInteger = fromIntegral
#-}

-- Work around `agda2hs` limitations.

certificate : Block → Maybe Certificate
certificate record{certificate = just c}  = Just c
certificate record{certificate = nothing} = Nothing

-- The actual model ---

record NodeModel : Set where
  field
    clock            : SlotNumber
    protocol         : PerasParams
    allChains        : List Chain
    allVotes         : List Vote
    allSeenCerts     : List Certificate

open NodeModel public

{-# COMPILE AGDA2HS NodeModel deriving (Eq, Show) #-}

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

preferredChain : PerasParams → List Certificate → List Chain → Chain
preferredChain params certs =
  maximumBy genesisChain (comparing (chainWeight (fromNat (perasB params)) certs))

{-# COMPILE AGDA2HS preferredChain #-}

postulate
  makeVote : PerasParams → SlotNumber → Block → Maybe Vote

{-# FOREIGN AGDA2HS
makeVote :: PerasParams -> SlotNumber -> Block -> Maybe Vote
makeVote protocol@MkPerasParams{perasT} slot block = do
  let r = slotToRound protocol slot
      party = mkCommitteeMember (mkParty 1 mempty [0..10000]) protocol (slot - fromIntegral perasT) True
  Right proof <- createMembershipProof r (Set.singleton party)
  Right vote  <- createSignedVote party r (hash block) proof 1
  pure vote
#-}

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

makeVote' : NodeModel → Maybe Vote
makeVote' s = do
  block ← listToMaybe (dropWhile (not ∘ blockOldEnough params slot) pref)
  let vr1A = nextRound (round cert') == r
      vr1B = extends block cert' (allChains s)
      vr2A = getRoundNumber r >= getRoundNumber (round cert') + perasR params
      vr2B = r > round certS && mod (getRoundNumber r) (perasK params) == mod (getRoundNumber (round certS)) (perasK params)
  guard (vr1A && vr1B || vr2A && vr2B)
  makeVote params slot block
  where
    params = protocol s
    slot   = clock s
    r      = slotToRound params slot
    pref = preferredChain params (allSeenCerts s) (allChains s)
    cert' = maximumBy genesisCert (comparing round) (allSeenCerts s)
    certS = maximumBy genesisCert (comparing round) (catMaybes (map certificate pref))

{-# COMPILE AGDA2HS makeVote' #-}

makeVote'' : NodeModel → Maybe Bool
makeVote'' = pure ∘ maybe False (const True) ∘ makeVote'

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

postulate
  checkVoteSignature : Vote → Bool

{-# FOREIGN AGDA2HS
checkVoteSignature :: Vote -> Bool
checkVoteSignature _ = True -- TODO: could do actual crypto here
#-}

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
  guard (checkVoteSignature v)
  checkVotingRules <- makeVote'' s
  guard (checkVotingRules)
  Just ([] , record s { allVotes = v ∷ allVotes s })

{-# COMPILE AGDA2HS transition #-}
