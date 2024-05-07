module Peras.QCD.Node.Model where

open import Data.Nat using (ℕ)
open import Haskell.Prelude
open import Peras.QCD.State

{-# FOREIGN AGDA2HS
{-# LANGUAGE DeriveGeneric #-}
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS (empty)
import Data.Default (Default(..))
import GHC.Generics (Generic)
import Numeric.Natural (Natural)
import Peras.Orphans ()
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

-- Utilities.

eqOn : ⦃ _ : Eq b ⦄ → (a → b) → a → a → Bool
eqOn f x y = f x == f y
{-# COMPILE AGDA2HS eqOn #-}

-- Cryptography types.

postulate
  ByteString : Set
  emptyBS : ByteString
  eqBS : ByteString → ByteString → Bool
{-# FOREIGN AGDA2HS
emptyBS :: ByteString
emptyBS = BS.empty
eqBS :: ByteString -> ByteString -> Bool
eqBS = (==)
#-}
{-# COMPILE GHC ByteString = type BS.ByteString #-}
{-# COMPILE GHC emptyBS = BS.empty #-}
{-# COMPILE GHC eqBS = (==) #-}

instance
  iByteStringEq : Eq ByteString
  iByteStringEq ._==_ = eqBS
  
record Hash (a : Set) : Set where
  field hashBytes : ByteString
open Hash public
{-# COMPILE AGDA2HS Hash newtype deriving (Generic, Show) #-}

instance
  iHashEq : Eq (Hash a)
  iHashEq ._==_ = eqOn hashBytes
{-# COMPILE AGDA2HS iHashEq #-}

record Hashable (a : Set) : Set where
  field hash : a → Hash a
open Hashable public
{-# COMPILE AGDA2HS Hashable class #-}

record MembershipProof : Set where
  field membershipProofBytes : ByteString
open MembershipProof public
{-# COMPILE AGDA2HS MembershipProof newtype deriving (Generic, Show) #-}

instance
  iMembershipProofEq : Eq MembershipProof
  iMembershipProofEq ._==_ = eqOn membershipProofBytes
{-# COMPILE AGDA2HS iMembershipProofEq #-}

record LeadershipProof : Set where
  field leadershipProofBytes : ByteString
open LeadershipProof public
{-# COMPILE AGDA2HS LeadershipProof newtype deriving (Generic, Show) #-}

instance
  iLeadershipProofEq : Eq LeadershipProof
  iLeadershipProofEq ._==_ = eqOn leadershipProofBytes
{-# COMPILE AGDA2HS iLeadershipProofEq #-}

record Signature : Set where
  field signatureBytes : ByteString
open Signature public
{-# COMPILE AGDA2HS Signature newtype deriving (Generic, Show) #-}

instance
  iSignatureEq : Eq Signature
  iSignatureEq ._==_ = eqOn signatureBytes
{-# COMPILE AGDA2HS iSignatureEq #-}

record VerificationKey : Set where
  field verificationKeyBytes : ByteString
open VerificationKey public
{-# COMPILE AGDA2HS VerificationKey newtype deriving (Generic, Show) #-}

instance
  iVerificationKeyEq : Eq VerificationKey
  iVerificationKeyEq ._==_ = eqOn verificationKeyBytes
{-# COMPILE AGDA2HS iVerificationKeyEq #-}

-- Basics.

Slot = ℕ
{-# COMPILE AGDA2HS Slot #-}

Round = ℕ
{-# COMPILE AGDA2HS Round #-}

PartyId = VerificationKey
{-# COMPILE AGDA2HS PartyId #-}

-- Blocks.

record Certificate : Set

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

duplicateVote : Vote → Vote → Bool
duplicateVote x y = eqOn voteRound x y && eqOn voteParty x y
{-# COMPILE AGDA2HS duplicateVote #-}

equivocatedVote : Vote → Vote → Bool
equivocatedVote x y = eqOn voteRound x y && eqOn voteParty x y && not (eqOn voteBlock x y)
{-# COMPILE AGDA2HS equivocatedVote #-}

-- Messages.

data Message : Set where
  NewChain : Chain → Message
  NewVote : Vote → Message
  NewCertificate : Certificate → Message
open Message public
{-# COMPILE AGDA2HS Message deriving (Generic, Show) #-}

-- Instances.

instance
  iVoteEq : Eq Vote
  iVoteEq ._==_ x y = eqOn voteRound x y
                        && eqOn voteParty x y
                        && eqOn voteBlock x y
                        && eqOn voteProof x y
                        && eqOn voteSignature x y
{-# COMPILE AGDA2HS iVoteEq #-}

instance
  iCertificateEq : Eq Certificate
  iCertificateEq ._==_ x y = eqOn certificateRound x y && eqOn certificateBlock x y
{-# COMPILE AGDA2HS iCertificateEq #-}

instance
  iBlockEq : Eq Block
  iBlockEq ._==_ x y = eqOn slot x y
                         && eqOn creator x y
                         && eqOn parent x y
                         && eqOn certificate x y
                         && eqOn leadershipProof x y
                         && eqOn bodyHash x y
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
  iBlockBodyEq ._==_ x y = eqOn headerHash x y && eqOn payload x y
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

-- State monad for node model.

NodeOperation = State NodeModel (List Message)
{-# COMPILE AGDA2HS NodeOperation #-}

NodeModification = State NodeModel ⊤
{-# COMPILE AGDA2HS NodeModification #-}

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

-- Cryptographic functions.

SignBlock =  Slot → PartyId → Hash Block → Maybe Certificate → Block
{-# COMPILE AGDA2HS SignBlock #-}

SignVote = Round → PartyId → Hash Block → Vote
{-# COMPILE AGDA2HS SignVote #-}

-- Arithmetic on slots and rounds.

incrementSlot : Slot → Slot
incrementSlot s = s + 1
{-# COMPILE AGDA2HS incrementSlot #-}

incrementRound : Round → Round
incrementRound r = r + 1
{-# COMPILE AGDA2HS incrementRound #-}

-- List operations.

checkDescending : (a → a → Ordering) → List a → Bool
checkDescending _ [] = True
checkDescending _ (x ∷ []) = True
checkDescending f (x ∷ y ∷ zs) = f x y == GT && checkDescending f (y ∷ zs)
{-# COMPILE AGDA2HS checkDescending #-}

insertDescending : (a → a → Ordering) → a → List a → List a
insertDescending _ x [] = x ∷ []
insertDescending f x (y ∷ ys) = case f x y of λ where
                                  LT → y ∷ insertDescending f x ys
                                  EQ → y ∷ ys -- Is it safe to ignore equivocations?
                                  GT → x ∷ y ∷ ys
{-# COMPILE AGDA2HS insertDescending #-}

unionDescending : ⦃ _ : Ord b ⦄ → (a → b) → List a → List a → List a
unionDescending f xs ys = foldr (insertDescending (λ x y → compare (f x) (f y))) ys xs
{-# COMPILE AGDA2HS unionDescending #-}

{-# TERMINATING #-}
groupBy : (a → a → Bool) → List a → List (List a)
groupBy _ [] = []
groupBy f (x ∷ xs) = let (ys , zs) = span (f x) xs
                     in (x ∷ ys) ∷ groupBy f zs
{-# COMPILE AGDA2HS groupBy #-}   

count : List a → ℕ
count _ = 0
{-# COMPILE AGDA2HS count #-}

-- Diffusion of messages.

diffuse : NodeOperation
diffuse = pure []
{-# COMPILE AGDA2HS diffuse #-}

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
    let noCertificate : List Round → Vote → Bool
        noCertificate ignoreRounds vote = notElem (voteRound vote) ignoreRounds
    let groupByRound : List Vote → List (List Vote)
        groupByRound = groupBy $ eqOn voteRound
    let hasQuorum : List a → Bool
        hasQuorum votes = count votes >= tau
    let getRound : List Vote → Round
        getRound votes = case votes of λ where -- FIXME: We cannot pattern match on constructors in `let`s?
                           [] → zero
                           (vote ∷ _) → voteRound vote
    roundsWithCerts ← fmap certificateRound <$> use certs
    fmap getRound
      ∘ filter hasQuorum
      ∘ groupByRound
      ∘ filter (noCertificate roundsWithCerts)
      <$> use votes
{-# COMPILE AGDA2HS roundsWithNewQuorums #-}

updateVotes : List Vote → NodeModification
updateVotes newVotes =
  do
    votes ≕ unionDescending voteRound newVotes
    -- FIXME: Work in progress.
    rs <- roundsWithNewQuorums
    pure tt
{-# COMPILE AGDA2HS updateVotes #-}

fetching : List Chain → List Vote → NodeOperation
fetching newChains newVotes =
  do
    currentSlot ≕ incrementSlot
    updateChains newChains
    updateVotes newVotes
    diffuse
{-# COMPILE AGDA2HS fetching #-}

{-
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
