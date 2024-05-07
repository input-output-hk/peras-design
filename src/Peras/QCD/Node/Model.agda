module Peras.QCD.Node.Model where

open import Data.Nat using (ℕ)
open import Haskell.Prelude
open import Peras.QCD.Crypto
open import Peras.QCD.State
open import Peras.QCD.Util

{-# FOREIGN AGDA2HS
{-# LANGUAGE DeriveGeneric #-}
import Data.Default (Default(..))
import GHC.Generics (Generic)
zero :: Natural
zero = 0
#-}

{-# FOREIGN GHC
import qualified Data.ByteString as BS
#-}

-- Protocol parameters.

data ParamSymbol : Set where
  U : ParamSymbol  -- the length (in slots) of a voting round
  A : ParamSymbol  -- max. age for including vote certificate
  W : ParamSymbol  -- weight to cut off for common prefix
  L : ParamSymbol  -- the cutoff window (in slots) which is ignored to select block to vote for in a round
  B : ParamSymbol  -- weight boost per vote certificate
  Τ : ParamSymbol  -- number of votes required for quorum
  R : ParamSymbol  -- chain-ignorance period
  K : ParamSymbol  -- the length of a cooldown period (in voting rounds)
{-# COMPILE AGDA2HS ParamSymbol #-}

τ : ParamSymbol  -- number of votes required for quorum
τ = Τ
{-# COMPILE AGDA2HS τ #-}

record Params : Set where
  field paramU : ℕ  -- the length (in slots) of a voting round
        paramA : ℕ  -- max. age for including vote certificate
        paramW : ℕ  -- weight to cut off for common prefix
        paramL : ℕ  -- the cutoff window (in slots) which is ignored to select block to vote for in a round
        paramB : ℕ  -- weight boost per vote certificate
        paramΤ : ℕ  -- number of votes required for quorum
        paramR : ℕ  -- chain-ignorance period
        paramK : ℕ  -- the length of a cooldown period (in voting rounds)
        
open Params public
{-# COMPILE AGDA2HS Params deriving (Eq, Generic, Ord, Show) #-}

defaultParams : Params
defaultParams =
  record {
    paramU = 120
  ; paramA = 240
  ; paramW = 3600
  ; paramL = 120
  ; paramB = 10
  ; paramΤ = 300
  ; paramR = 120
  ; paramK = 600
  }
{-# COMPILE AGDA2HS defaultParams #-}
{-# FOREIGN AGDA2HS
instance Default Params where
  def = defaultParams
#-}

-- FIXME: Use a proxy so that parameters may have types other than ℕ.
perasParam : ParamSymbol → Params → ℕ
perasParam U = paramU
perasParam A = paramA
perasParam W = paramW
perasParam L = paramL
perasParam B = paramB
perasParam Τ = paramΤ
perasParam R = paramR
perasParam K = paramK
{-# COMPILE AGDA2HS perasParam #-}

-- Cryptography types.

record MembershipProof : Set where
  field membershipProofBytes : ByteString
open MembershipProof public
{-# COMPILE AGDA2HS MembershipProof newtype deriving (Generic, Show) #-}

record LeadershipProof : Set where
  field leadershipProofBytes : ByteString
open LeadershipProof public
{-# COMPILE AGDA2HS LeadershipProof newtype deriving (Generic, Show) #-}

record Signature : Set where
  field signatureBytes : ByteString
open Signature public
{-# COMPILE AGDA2HS Signature newtype deriving (Generic, Show) #-}

record VerificationKey : Set where
  field verificationKeyBytes : ByteString
open VerificationKey public
{-# COMPILE AGDA2HS VerificationKey newtype deriving (Generic, Show) #-}

-- Basics.

Slot : Set
Slot = ℕ
{-# COMPILE AGDA2HS Slot #-}

Round : Set
Round = ℕ
{-# COMPILE AGDA2HS Round #-}

PartyId : Set
PartyId = VerificationKey
{-# COMPILE AGDA2HS PartyId #-}

-- Blocks.

record Certificate : Set

Tx : Set
Tx = ⊤
{-# COMPILE AGDA2HS Tx #-}

record Block : Set where
  constructor MakeBlock
  field slot : Slot
        creator : PartyId
        parent : Hash Block
        certificate : Maybe Certificate
        leadershipProof : LeadershipProof
        signature : Signature
        bodyHash : Hash (List Tx)
open Block public
{-# COMPILE AGDA2HS Block deriving (Generic, Show) #-}

record BlockBody : Set where
  field headerHash : Hash Block
        payload : List Tx
open BlockBody public
{-# COMPILE AGDA2HS BlockBody deriving (Generic, Show) #-}

-- Chains.

data Chain : Set where
  Genesis : Chain
  ChainBlock : Block → Chain → Chain
{-# COMPILE AGDA2HS Chain deriving (Generic, Show) #-}

genesisHash : Hash Block
genesisHash = record {hashBytes = emptyBS}
{-# COMPILE AGDA2HS genesisHash #-}

-- Certificates.

record Certificate where
  constructor MakeCertificate
  field certificateRound : Round
        certificateBlock : Hash Block
open Certificate public
{-# COMPILE AGDA2HS Certificate deriving (Generic, Show) #-}

genesisCert : Certificate
genesisCert = MakeCertificate 0 genesisHash
{-# COMPILE AGDA2HS genesisCert #-}

-- Votes.

record Vote : Set where
  field voteRound : ℕ
        voteParty : PartyId
        voteBlock : Hash Block
        voteProof : MembershipProof
        voteSignature : Signature
open Vote public
{-# COMPILE AGDA2HS Vote deriving (Generic, Show) #-}

-- Messages.

data Message : Set where
  NewChain : Chain → Message
  NewVote : Vote → Message
  NewCertificate : Certificate → Message
open Message public
{-# COMPILE AGDA2HS Message deriving (Generic, Show) #-}

-- Instances.

instance
  iMembershipProofEq : Eq MembershipProof
  iMembershipProofEq ._==_ = eqByBS membershipProofBytes
{-# COMPILE AGDA2HS iMembershipProofEq #-}

instance
  iLeadershipProofEq : Eq LeadershipProof
  iLeadershipProofEq ._==_ = eqByBS leadershipProofBytes
{-# COMPILE AGDA2HS iLeadershipProofEq #-}

instance
  iSignatureEq : Eq Signature
  iSignatureEq ._==_ = eqByBS signatureBytes
{-# COMPILE AGDA2HS iSignatureEq #-}

instance
  iVerificationKeyEq : Eq VerificationKey
  iVerificationKeyEq ._==_ = eqByBS verificationKeyBytes
{-# COMPILE AGDA2HS iVerificationKeyEq #-}

instance
  iVoteEq : Eq Vote
  iVoteEq ._==_ x y = eqBy voteRound x y
                        && eqBy voteParty x y
                        && eqBy voteBlock x y
                        && eqBy voteProof x y
                        && eqBy voteSignature x y
{-# COMPILE AGDA2HS iVoteEq #-}

instance
  iCertificateEq : Eq Certificate
  iCertificateEq ._==_ x y = eqBy certificateRound x y && eqBy certificateBlock x y
{-# COMPILE AGDA2HS iCertificateEq #-}

instance
  iBlockEq : Eq Block
  iBlockEq ._==_ x y = eqBy slot x y
                         && eqBy creator x y
                         && eqBy parent x y
                         && eqBy certificate x y
                         && eqBy leadershipProof x y
                         && eqBy bodyHash x y
{-# COMPILE AGDA2HS iBlockEq #-}

instance
  iBlockHashable : Hashable Block
  iBlockHashable = record {
      hash = λ b →
        let record { signatureBytes = s } = signature b
        in record { hashBytes = s }
    }
{-# COMPILE AGDA2HS iBlockHashable #-}

instance
  iBlockBodyEq : Eq BlockBody
  iBlockBodyEq ._==_ x y = eqBy headerHash x y && eqBy payload x y
{-# COMPILE AGDA2HS iBlockBodyEq #-}

instance
  iChainEq : Eq Chain
  iChainEq ._==_ Genesis Genesis = True
  iChainEq ._==_ (ChainBlock b c) (ChainBlock b' c') = b == b' && c == c'
  iChainEq ._==_ _ _ = False
{-# COMPILE AGDA2HS iChainEq #-}

tipHash : Chain → Hash Block
tipHash Genesis = genesisHash
tipHash (ChainBlock block _) = hash iBlockHashable block
{-# COMPILE AGDA2HS tipHash #-}

instance
  iMessageEq : Eq Message
  iMessageEq ._==_ (NewChain x) (NewChain y) = x == y
  iMessageEq ._==_ (NewVote x) (NewVote y) = x == y
  iMessageEq ._==_ (NewCertificate x) (NewCertificate y) = x == y
  iMessageEq ._==_ _ _ = False
{-# COMPILE AGDA2HS iMessageEq #-}

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

-- Cryptographic functions.

SignBlock : Set
SignBlock =  Slot → PartyId → Hash Block → Maybe Certificate → Block
{-# COMPILE AGDA2HS SignBlock #-}

SignVote : Set
SignVote = Round → PartyId → Hash Block → Vote
{-# COMPILE AGDA2HS SignVote #-}

-- Executable specification.

initialize : Params → PartyId → NodeOperation
initialize params party =
  do
    protocol ≔ params
    creatorId ≔ party
    diffuse
{-# COMPILE AGDA2HS initialize #-}

updateChains : List Chain → NodeModification
updateChains newChains =
  do
    -- FIXME: Work in progress.
    pure tt
{-# COMPILE AGDA2HS updateChains #-}

roundsWithNewQuorums : State NodeModel (List Round)
roundsWithNewQuorums =
  do
    tau ← peras τ
    roundsWithCerts ← use certs ⇉ fmap certificateRound
    use votes
      ⇉ filter (hasNoCertificate roundsWithCerts)
      ⇉ groupByRound
      ⇉ filter (hasQuorum tau)
      ⇉ fmap getRound
  where
    hasNoCertificate : List Round → Vote → Bool
    hasNoCertificate ignoreRounds vote = notElem (voteRound vote) ignoreRounds
    groupByRound : List Vote → List (List Vote)
    groupByRound = groupBy (eqBy voteRound)
    hasQuorum : ℕ → List a → Bool
    hasQuorum tau votes' = count votes' >= tau
    getRound : List Vote → Round
    getRound [] = zero
    getRound (vote ∷ _) = voteRound vote
{-# COMPILE AGDA2HS roundsWithNewQuorums #-}

fetching : List Chain → List Vote → NodeOperation
fetching newChains newVotes =
  do
    currentSlot ≕ addOne
    updateChains newChains
    votes ≕ insertVotes newVotes
    diffuse
  where
    insertVotes : List Vote → List Vote → List Vote
    insertVotes = unionDescending voteRound
{-# COMPILE AGDA2HS fetching #-}

{-
newRound : NodeOperation
newRound =
  do
    currentRound ≕ addOne
    messages
{-# COMPILE AGDA2HS newRound #-}

forgeBlock : HashTip → SignBlock → NodeOperation
forgeBlock hashTip signBlock =
  do
    chain ← use preferredChain
    parentHash ← pure $ hashTip chain
    cert ← pure nothing  -- FIXME: Add certificate logic.
    block ← signBlock <$> use currentSlot <*> use creatorId <*> pure parentHash <*> pure cert
    chain' ← pure $ block ∷ chain
    preferredChain ≔ chain'
    messages ↞ NewChain chain'
-- FIXME: Consider revising notation.
--   * `pure $` could be written as a unary operator like `!`, but `agda2hs` doesn't support that.
--   * `<$> use` could be written as something like `<$>>` to eliminate the need for `use`.
--   * `<$> pure` could be written as something like `<$!` to eliminate the need for `pure`
--   * `use` could also be witeen as a unary operator, but once again `agda2hs` doesn't support that.
{-# COMPILE AGDA2HS forgeBlock #-}


pointsTo : Certificate → Chain → Bool
pointsTo cert chain =
  any found chain
  where
    found : Block → Bool
    found block = case certificate block of λ where
                    nothing → False
                    (just cert') → True -- cert == cert'
{-# COMPILE AGDA2HS pointsTo #-}

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

-}
