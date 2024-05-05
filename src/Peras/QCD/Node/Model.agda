module Peras.QCD.Node.Model where

open import Data.Nat using (ℕ)

open import Haskell.Prelude

open import Peras.Block using (Block; Certificate; PartyId; Slot; votingRoundNumber)
open import Peras.Chain using (Chain; MkRoundNumber; RoundNumber; Vote; roundNumber; votingRound)
open import Peras.Crypto using (Hash; Hashable)
open import Peras.Message using (Message; NewChain)

open import Peras.QCD.State

{-# FOREIGN AGDA2HS
{-# LANGUAGE DeriveGeneric #-}
import Data.Default (Default(..))
import GHC.Generics (Generic)
import Peras.Orphans ()
#-}

-- Protocol parameters.

record Params : Set where
  field paramU : ℕ  -- round length
        paramL : ℕ  -- cutoff window
        paramA : ℕ  -- vote expiration
        
open Params public
{-# COMPILE AGDA2HS Params deriving (Eq, Generic, Ord, Show) #-}

defaultParams : Params
defaultParams =
  record {
    paramU = 120
  ; paramL = 10
  ; paramA = 240
  }
{-# COMPILE AGDA2HS defaultParams #-}
{-# FOREIGN AGDA2HS
instance Default Params where
  def = defaultParams
#-}

-- Cryptographic functions.

HashBlock = Block → Hash Block
{-# COMPILE AGDA2HS HashBlock #-}

HashTip = Chain → Hash Block
{-# COMPILE AGDA2HS HashTip #-}

SignBlock =  Slot → PartyId → Hash Block → Maybe Certificate → Block
{-# COMPILE AGDA2HS SignBlock #-}

SignVote = RoundNumber → PartyId → Hash Block → Vote
{-# COMPILE AGDA2HS SignVote #-}

record CryptoFunctions : Set where
  field
    hashBlockFunction : HashBlock
    hashTipFunction : HashTip
    signBlockFunction : SignBlock
    signVoteFunction : SignVote
open CryptoFunctions public
{-# COMPILE AGDA2HS CryptoFunctions #-}

-- Node model.

record NodeModel : Set where
  field nodeProtocol : Params
        nodeCreatorId : PartyId
        nodeCurrentSlot : Slot
        nodeCurrentRound : RoundNumber
        nodePreferredChain : Chain
        nodePreferredCerts : List Certificate
        nodePreferredVotes : List Vote
open NodeModel public
{-# COMPILE AGDA2HS NodeModel deriving (Eq, Generic, Ord, Show) #-}

emptyNode : NodeModel
emptyNode =
  record {
    nodeProtocol = defaultParams
  ; nodeCreatorId = 0
  ; nodeCurrentSlot = 0
  ; nodeCurrentRound = MkRoundNumber 0
  ; nodePreferredChain = []
  ; nodePreferredCerts = []
  ; nodePreferredVotes = []
  }
{-# COMPILE AGDA2HS emptyNode #-}

{-# FOREIGN AGDA2HS
instance Default NodeModel where
  def = emptyNode
#-}

-- State monad for node model.

NodeOperation = State NodeModel (List Message)
{-# COMPILE AGDA2HS NodeOperation #-}

NodeModification = State NodeModel ⊤
{-# COMPILE AGDA2HS NodeModification #-}

-- Lenses for node model.

protocol : Lens' NodeModel Params
protocol = lens' nodeProtocol (λ s x → record s {nodeProtocol = x})
{-# COMPILE AGDA2HS protocol #-}

peras : (Params → a) → State NodeModel a
peras x = x <$> use protocol
{-# COMPILE AGDA2HS peras #-}

creatorId : Lens' NodeModel PartyId
creatorId = lens' nodeCreatorId (λ s x → record s {nodeCreatorId = x})
{-# COMPILE AGDA2HS creatorId #-}

currentSlot : Lens' NodeModel Slot
currentSlot = lens' nodeCurrentSlot (λ s x → record s {nodeCurrentSlot = x})
{-# COMPILE AGDA2HS currentSlot #-}

currentRound : Lens' NodeModel RoundNumber
currentRound = lens' nodeCurrentRound (λ s x → record s {nodeCurrentRound = x})
{-# COMPILE AGDA2HS currentRound #-}

preferredChain : Lens' NodeModel Chain
preferredChain = lens' nodePreferredChain (λ s x → record s {nodePreferredChain = x})
{-# COMPILE AGDA2HS preferredChain #-}

preferredCerts : Lens' NodeModel (List Certificate)
preferredCerts = lens' nodePreferredCerts (λ s x → record s {nodePreferredCerts = x})
{-# COMPILE AGDA2HS preferredCerts #-}

preferredVotes : Lens' NodeModel (List Vote)
preferredVotes = lens' nodePreferredVotes (λ s x → record s {nodePreferredVotes = x})
{-# COMPILE AGDA2HS preferredVotes #-}

-- Arithmetic on slots and rounds.

incrementSlot : Slot → Slot
incrementSlot s = s + 1
{-# COMPILE AGDA2HS incrementSlot #-}

incrementRound : RoundNumber → RoundNumber
incrementRound (MkRoundNumber r) = MkRoundNumber (r + 1)
{-# COMPILE AGDA2HS incrementRound #-}

-- Messages.

messages : NodeOperation
messages = pure []
{-# COMPILE AGDA2HS messages #-}

_↞_ : ⦃ _ : Applicative f ⦄ → f (List a) → a → f (List a)
_↞_ m x = fmap (λ xs → xs ++ (x ∷ [])) m
infixl 30 _↞_
{-# COMPILE AGDA2HS _↞_ #-}
{-# FOREIGN AGDA2HS
infixl 5 ↞
#-}

-- Executable specification.

initialize : Params → PartyId → NodeOperation
initialize params party =
  do
    protocol ≔ params
    creatorId ≔ party
    messages
{-# COMPILE AGDA2HS initialize #-}

discardExpiredCerts : NodeModification
discardExpiredCerts =
  do
    now ← use currentSlot
    u ← peras paramU
    a ← peras paramA
    let expired : Certificate → Bool
        expired cert = u * votingRoundNumber cert + a < now
    preferredCerts ≕ filter (not ∘ expired)
{-# COMPILE AGDA2HS discardExpiredCerts #-}

discardExpiredVotes : NodeModification
discardExpiredVotes =
  do
    now ← use currentSlot
    u ← peras paramU
    a ← peras paramA
    let expired : Vote → Bool
        expired vote = u * roundNumber (votingRound vote) + a < now
    preferredVotes ≕ filter (not ∘ expired)
{-# COMPILE AGDA2HS discardExpiredVotes #-}

newSlot : NodeOperation
newSlot =
  do
    currentSlot ≕ incrementSlot
    discardExpiredCerts
    discardExpiredVotes
    messages
{-# COMPILE AGDA2HS newSlot #-}

newRound : NodeOperation
newRound =
  do
    currentRound ≕ incrementRound
    messages
{-# COMPILE AGDA2HS newRound #-}

forgeBlock : HashTip → SignBlock → NodeOperation
forgeBlock hashTip signBlock =
  do
    chain ← use preferredChain
    parentHash ← pure $ hashTip chain
    cert ← pure Nothing  -- FIXME: Add certificate logic.
    block ← signBlock <$> use currentSlot <*> use creatorId <*> pure parentHash <*> pure cert
    chain' ← pure $ block ∷ chain
    preferredChain ≔ chain'
    messages ↞ NewChain chain'
-- Notes on notation:
--   * `pure $` could be written as a unary operator like `!`, but `agda2hs` doesn't support that.
--   * `<$> use` could be written as something like `<$>>` to eliminate the need for `use`.
--   * `<$> pure` could be written as something like `<$!` to eliminate the need for `pure`
--   * `use` could also be witeen as a unary operator, but once again `agda2hs` doesn't support that.
{-# COMPILE AGDA2HS forgeBlock #-}




-- IGNORE THE FOLLOWING WORK IN PROGRESS

buildCert : NodeModel → List Message → NodeModel × List Message
buildCert node messages' = node , messages' -- FIXME: To be implemented.
{-# COMPILE AGDA2HS buildCert #-}

castVote : NodeModel → HashBlock → SignVote → NodeModel × List Message
castVote node hashBlock signVote =
  buildCert
    (record node {nodePreferredVotes = nodePreferredVotes node ++ vote})
    (map Message.SomeVote vote)
  where
    eligible : Block → Bool
    eligible block = Block.slotNumber block + paramL (nodeProtocol node) <= nodeCurrentSlot node
    vote = case filter eligible (nodePreferredChain node) of λ where
      [] → []
      (block ∷ _) → signVote (nodeCurrentRound node) (nodeCreatorId node) (hashBlock block) ∷ []
{-# COMPILE AGDA2HS castVote #-}


test1 : State NodeModel Slot
test1 =
  do
      i <- use currentSlot
      currentSlot ≔ (i + 1)
      currentSlot ≕ (λ j → j + 10)
      use currentSlot
{-# COMPILE AGDA2HS test1 #-}

-- State transitions.

data Signal : Set where
  Initialize : Params → PartyId → Signal
  NewSlot : Signal
  NewRound : Signal
  ForgeBlock : Signal
  CastVote : Signal
  ReceiveBlock : Block → Signal
  ReceiveVote : Vote → Signal
  ReceiveCertificate : Certificate → Signal
{-# COMPILE AGDA2HS Signal deriving (Eq, Generic, Ord, Show) #-}
