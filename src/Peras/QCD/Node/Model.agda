module Peras.QCD.Node.Model where

open import Data.Nat using (ℕ)
open import Haskell.Prelude
open import Peras.QCD.Crypto using (emptyBS)
open import Peras.QCD.Protocol
open import Peras.QCD.State
open import Peras.QCD.Types
open import Peras.QCD.Types.Instances

{-# FOREIGN AGDA2HS
{-# LANGUAGE DeriveGeneric #-}
import Data.Default (Default(..))
import GHC.Generics (Generic)
import Peras.QCD.Types.Instances ()
#-}

-- Node model.

record NodeModel : Set where
  field nodeProtocol : Params
        nodeCreatorId : PartyId
        nodeCurrentSlot : Slot
        nodeCurrentRound : Round
        nodePreferredChain : Chain
        nodeChains : List Chain
        nodeVotes : List Vote
        nodeCerts : List Certificate
        nodeLatestCertSeen : Certificate
        nodeLatestCertOnChain : Certificate
open NodeModel public
{-# COMPILE AGDA2HS NodeModel deriving (Generic, Show) #-}

emptyNode : NodeModel
emptyNode =
  record {
    nodeProtocol = defaultParams
  ; nodeCreatorId = record {verificationKeyBytes = emptyBS}
  ; nodeCurrentSlot = 0
  ; nodeCurrentRound =  0
  ; nodePreferredChain = Genesis
  ; nodeChains = Genesis ∷ []
  ; nodeVotes = []
  ; nodeCerts = genesisCert ∷ []  -- FIXME: This differs from the Peras paper.
  ; nodeLatestCertSeen = genesisCert
  ; nodeLatestCertOnChain = genesisCert
  }
{-# COMPILE AGDA2HS emptyNode #-}

{-# FOREIGN AGDA2HS
instance Default NodeModel where
  def = emptyNode
#-}

-- Lenses for node model.

protocol : Lens' NodeModel Params
protocol = lens' nodeProtocol (λ s x → record s {nodeProtocol = x})
{-# COMPILE AGDA2HS protocol #-}

peras : ParamSymbol → State NodeModel ℕ
peras x = perasParam x <$> use protocol
{-# COMPILE AGDA2HS peras #-}

creatorId : Lens' NodeModel PartyId
creatorId = lens' nodeCreatorId (λ s x → record s {nodeCreatorId = x})
{-# COMPILE AGDA2HS creatorId #-}

currentSlot : Lens' NodeModel Slot
currentSlot = lens' nodeCurrentSlot (λ s x → record s {nodeCurrentSlot = x})
{-# COMPILE AGDA2HS currentSlot #-}

currentRound : Lens' NodeModel Round
currentRound = lens' nodeCurrentRound (λ s x → record s {nodeCurrentRound = x})
{-# COMPILE AGDA2HS currentRound #-}

preferredChain : Lens' NodeModel Chain
preferredChain = lens' nodePreferredChain (λ s x → record s {nodePreferredChain = x})
{-# COMPILE AGDA2HS preferredChain #-}

chains : Lens' NodeModel (List Chain)
chains = lens' nodeChains (λ s x → record s {nodeChains = x})
{-# COMPILE AGDA2HS chains #-}

votes : Lens' NodeModel (List Vote)
votes = lens' nodeVotes (λ s x → record s {nodeVotes = x})
{-# COMPILE AGDA2HS votes #-}

certs : Lens' NodeModel (List Certificate)
certs = lens' nodeCerts (λ s x → record s {nodeCerts = x})
{-# COMPILE AGDA2HS certs #-}

latestCertSeen : Lens' NodeModel Certificate
latestCertSeen = lens' nodeLatestCertSeen (λ s x → record s {nodeLatestCertSeen = x})
{-# COMPILE AGDA2HS latestCertSeen #-}

latestCertOnChain : Lens' NodeModel Certificate
latestCertOnChain = lens' nodeLatestCertOnChain (λ s x → record s {nodeLatestCertOnChain = x})
{-# COMPILE AGDA2HS latestCertOnChain #-}

-- State monad for node model.

NodeState : Set → Set
NodeState s = State NodeModel s
{-# COMPILE AGDA2HS NodeState #-}

NodeOperation : Set
NodeOperation = NodeState (List Message)
{-# COMPILE AGDA2HS NodeOperation #-}

NodeModification : Set
NodeModification = NodeState ⊤
{-# COMPILE AGDA2HS NodeModification #-}

diffuse : NodeOperation
diffuse = pure []
{-# COMPILE AGDA2HS diffuse #-}

