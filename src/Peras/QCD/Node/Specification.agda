module Peras.QCD.Node.Specification where

open import Data.Nat using (ℕ)
open import Haskell.Prelude
open import Peras.QCD.Crypto
open import Peras.QCD.Crypto.Placeholders
open import Peras.QCD.Node.Model
open import Peras.QCD.Protocol
open import Peras.QCD.State
open import Peras.QCD.Types
open import Peras.QCD.Types.Instances
open import Peras.QCD.Util

{-# FOREIGN AGDA2HS
import Peras.QCD.Types.Instances ()
zero :: Natural
zero = 0
#-}

-- Executable specification.

-- Set the protocol parameters and identity of a node.
initialize : Params → PartyId → NodeOperation
initialize params party =
  do
    -- Set the protocol parameters.
    protocol ≔ params
    -- Record the identity of the party operating the node.
    creatorId ≔ party
    -- There are no messages to diffuse.
    diffuse
{-# COMPILE AGDA2HS initialize #-}

-- Find the hash of a chain's tip.
chainTip : Chain → Hash Block
chainTip Genesis = genesisHash
chainTip (ChainBlock block _) = hash iBlockHashable block
{-# COMPILE AGDA2HS chainTip #-}

-- Extend a chain.
extendChain : Block → Chain → Chain
extendChain = ChainBlock
{-# COMPILE AGDA2HS extendChain #-}

-- Determine whether one chain is a prefix on another chain.
isChainPrefix : Chain → Chain → Bool
isChainPrefix Genesis _ = True
isChainPrefix (ChainBlock block _) chain' =
  test (chainBlocks chain')
  where sl : Slot
        sl = slot block
        hb : Hash Block
        hb = hash iBlockHashable block
        test : List Block → Bool
        test [] = False
        test (b ∷ bs) =
          let sl' = slot b
              hb' = parent b
          in hb == hb' || sl < sl' && test bs
{-# COMPILE AGDA2HS isChainPrefix #-}

-- Update the sets of chains and certificates with a new chain.
updateChains : List Chain → NodeModification
updateChains newChains =
  do
    -- Store the new certificates.
    certs ≕ insertCerts (concatMap certsOnChain newChains)
    -- Remove any old chains that are prefixes to the new chains.
    chains ≕ filter (not ∘ isPrefixOfAnyChain newChains)
    -- Find the new chains that are not prefixes of old ones.
    isPrefixOfOldChains ← use chains ⇉ isPrefixOfAnyChain
    chains ≕ mappend (filter (not ∘ isPrefixOfOldChains) newChains)
  where
    -- Merge two lists of certificates, keeping their round numbers sorted in decreasing order.
    insertCerts : List Certificate → List Certificate → List Certificate
    insertCerts = unionDescending certificateRound
    -- Determine whether a chain is a prefix of any in a list of chains.
    isPrefixOfAnyChain : List Chain → Chain → Bool
    isPrefixOfAnyChain chains' chain = any (isChainPrefix chain) chains'
{-# COMPILE AGDA2HS updateChains #-}

-- Find the weight of a chain, given a set of certificates.
chainWeight : ℕ → List Certificate → Chain → ℕ
chainWeight boost certs' chain =
  let blocks = chainBlocks chain ⇉ hash iBlockHashable
      certifieds = certs' ⇉ certificateBlock
      z = filter (flip elem certifieds) blocks
  in count blocks + boost * count z
{-# COMPILE AGDA2HS chainWeight #-}

-- Find the heaviest of a list of chains, given a set of certificates.
heaviestChain : ℕ → List Certificate → List Chain → Chain
heaviestChain _ _ [] = Genesis
heaviestChain boost certs' (chain ∷ chains') = heaviest (chain , chainWeight boost certs' chain) chains'
  where heaviest : Chain × ℕ → List Chain → Chain
        heaviest ( c , _ ) [] = c
        heaviest ( c , w ) (c' ∷ cs) =
          let w' = chainWeight boost certs' c'
          in if w <= w' -- The Peras paper is ambiguous with respect to ties.
             then heaviest ( c' , w') cs
             else heaviest ( c , w) cs
{-# COMPILE AGDA2HS heaviestChain #-}

-- Build certificates for rounds that have a new quorum.
certificatesForNewQuorums : State NodeModel (List Certificate)
certificatesForNewQuorums =
  do
    -- Fetch the requirement for a quorum.
    tau ← peras τ
    -- Find which rounds already have certificates.
    roundsWithCerts ← use certs ⇉ fmap certificateRound
    -- Build certificates for rounds that have a new quorum.
    use votes
      ⇉ filter (hasNoCertificate roundsWithCerts)  -- Ignore votes that already have certificates.
      ⇉ groupByRound                               -- Group the votes by round.
      ⇉ filter (hasQuorum tau)                     -- Ignore rounds that don't have a quorum of votes.
      ⇉ fmap buildCertificate                      -- Build the certificates for the rounds with quorums.
  where
    -- Check whether a vote belongs to a round that already has a certificate.
    hasNoCertificate : List Round → Vote → Bool
    hasNoCertificate roundsWithCerts vote = notElem (voteRound vote) roundsWithCerts
    -- Group a list of votes by their round number.
    groupByRound  : List Vote → List (List Vote)
    groupByRound = groupBy (eqBy voteRound)
    -- Check if a group of votes in the same round constitutes a quorum.
    hasQuorum : ℕ → List a → Bool
    hasQuorum tau votes' = count votes' >= tau
{-# COMPILE AGDA2HS certificatesForNewQuorums #-}

-- Record the lastest certificate seen.
updateLatestCertSeen : NodeModification
updateLatestCertSeen =
  do
    latest ← use certs ⇉ firstWithDefault genesisCert
    latestCertSeen ≔ latest
{-# COMPILE AGDA2HS updateLatestCertSeen #-}

-- Record the latest certificate on the preferred chain.
updateLatestCertOnChain : NodeModification
updateLatestCertOnChain =
  do
    latest ← use preferredChain ⇉ lastCert
    latestCertOnChain ≔ latest
{-# COMPILE AGDA2HS updateLatestCertOnChain #-}

fetching : List Chain → List Vote → NodeOperation
fetching newChains newVotes =
  do
    -- At the beginning of each slot.
    currentSlot ≕ addOne
    -- Add any new chains and certificates.
    updateChains newChains
    -- Add new votes.
    votes ≕ insertVotes newVotes
    -- Turn any new quorums into certificates.
    newCerts ← certificatesForNewQuorums
    certs ≕ insertCerts newCerts
    -- Make the heaviest chain the preferred one.
    boost ← peras B
    heaviest ← heaviestChain boost <$> use certs <*> use chains
    preferredChain ≔ heaviest
    -- Record the latest certificate seen.
    updateLatestCertSeen
    -- Record the latest certificate on the preferred chain.
    updateLatestCertOnChain
    -- No messages need to be diffused.
    diffuse
  where
    -- Merge two lists of votes, keeping their round numbers sorted in decreasing order.
    insertVotes : List Vote → List Vote → List Vote
    insertVotes = unionDescending voteRound
    -- Merge two lists of certificates, keeping their round numbers sorted in decreasing order.
    insertCerts : List Certificate → List Certificate → List Certificate
    insertCerts = unionDescending certificateRound
{-# COMPILE AGDA2HS fetching #-}

blockCreation : List Tx → NodeOperation
blockCreation txs =
  do
    -- Find the hash of the parent's tip.
    parent ← use preferredChain ⇉ chainTip
    -- Create a certificate, if needed.
    let cert = Nothing -- FIXME: Implement.
    
    -- Forge the block.
    block ← signBlock <$> use currentSlot <*> use creatorId <*> pure parent <*> pure cert <*> pure txs
    -- Extend the preferred chain.
    chain ← use preferredChain ⇉ extendChain block
    -- Diffuse the new chain.
    diffuse ↞ NewChain chain
    
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
