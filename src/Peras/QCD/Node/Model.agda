module Peras.QCD.Node.Model where

open import Data.Nat using (ℕ)

open import Haskell.Prelude

open import Peras.Block using (Block; Certificate; PartyId; Slot)
open import Peras.Chain using (Chain; MkRoundNumber; RoundNumber; Vote)
open import Peras.Crypto using (Hash; Hashable)
open import Peras.Message using (Message)

{-# FOREIGN AGDA2HS
import Data.Default (Default(..))
import GHC.Generics (Generic)
#-}

record Params : Set where
  field paramU : ℕ  -- round length
        paramL : ℕ  -- cutoff window
open Params public
{-# COMPILE AGDA2HS Params deriving (Eq, Generic, Ord, Show) #-}

defaultParams : Params
defaultParams =
  record {
    paramU = 120
  ; paramL = 10
  }
{-# COMPILE AGDA2HS defaultParams #-}
{-# FOREIGN AGDA2HS
instance Default Params where
  def = defaultParams
#-}

HashBlock = Block → Hash Block
{-# COMPILE AGDA2HS HashBlock #-}

HashTip = Chain → Hash Block
{-# COMPILE AGDA2HS HashTip #-}

IsHonest = Bool
{-# COMPILE AGDA2HS IsHonest #-}

record NodeModel : Set where
  field protocol : Params
        self : PartyId
        nowSlot : Slot
        nowRound : RoundNumber
        honest : IsHonest
        preferredChain : Chain
        preferredCerts : List Certificate
        preferredVotes : List Vote
open NodeModel public
{-# COMPILE AGDA2HS NodeModel deriving (Eq, Generic, Ord, Show) #-}

emptyNode : NodeModel
emptyNode =
  record {
    protocol = defaultParams
  ; self = 0
  ; nowSlot = 0
  ; nowRound = MkRoundNumber 0
  ; honest = True
  ; preferredChain = []
  ; preferredCerts = []
  ; preferredVotes = []
  }
{-# COMPILE AGDA2HS emptyNode #-}

{-# FOREIGN AGDA2HS
instance Default NodeModel where
  def = emptyNode
#-}

MakeBlock = Slot → PartyId → Hash Block → Maybe Certificate → Block
{-# COMPILE AGDA2HS MakeBlock #-}

MakeVote = RoundNumber → PartyId → Hash Block → Vote
{-# COMPILE AGDA2HS MakeVote #-}

-- State transition.

data Signal : Set where
  Initialize : Params → PartyId → IsHonest → Signal
  NewSlot : Signal
  NewRound : Signal
  ForgeBlock : MakeBlock → Signal
  CastVote : MakeVote → Signal
  ReceiveBlock : Block → Signal
  ReceiveVote : Vote → Signal
  ReceiveCertificate : Certificate → Signal
{-# COMPILE AGDA2HS Signal deriving (Eq, Generic, Ord, Show) #-}

-- Executable specification.

initialize : NodeModel → Params → PartyId → IsHonest → NodeModel × List Message
initialize node params party honesty =
  record node {
    protocol = params
  ; self = party
  ; honest = honesty
  } , []
{-# COMPILE AGDA2HS initialize #-}

newSlot : NodeModel → NodeModel × List Message
newSlot node = record node {nowSlot = nowSlot node + 1} , []
{-# COMPILE AGDA2HS newSlot #-}

newRound : NodeModel → NodeModel × List Message
newRound node = record node {nowRound = MkRoundNumber $ RoundNumber.roundNumber (nowRound node) + 1} , []
{-# COMPILE AGDA2HS newRound #-}

forgeBlock : NodeModel → HashTip → MakeBlock → NodeModel × List Message
forgeBlock node hashTip makeBlock =
  record node {preferredChain = chain'; preferredCerts = snd certs}, Message.NewChain chain' ∷ []
  where
    certs : Maybe Certificate × List Certificate
    certs = case preferredCerts node of λ where
      [] → Nothing , []
      (cert' ∷ certs) → Just cert' , certs
    prior = preferredChain node
    block = makeBlock (nowSlot node) (self node) (hashTip prior) (fst certs)
    chain' = block ∷ prior
{-# COMPILE AGDA2HS forgeBlock #-}

buildCert : NodeModel → List Message → NodeModel × List Message
buildCert node messages = _

castVote : NodeModel → HashBlock → MakeVote → NodeModel × List Message
castVote node hashBlock makeVote =
  buildCert
    (record node {preferredVotes = preferredVotes node ++ vote})
    (map Message.SomeVote vote)
  where
    eligible : Block → Bool
    eligible block = Block.slotNumber block + paramL (protocol node) <= nowSlot node
    vote = case filter eligible (preferredChain node) of λ where
      [] → []
      (block ∷ _) → makeVote (nowRound node) (self node) (hashBlock block) ∷ []
{-# COMPILE AGDA2HS castVote #-}
