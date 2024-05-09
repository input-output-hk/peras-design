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
    use votes                                      -- Fetch the votes.
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
    u ← peras U
    now ← use currentSlot
    currentRound ≔ integerDivide now u
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

-- Create a new block.
blockCreation : List Tx → NodeOperation
blockCreation txs =
  do
    -- Find the hash of the parent's tip.
    parent ← use preferredChain ⇉ chainTip
    -- Fetch the lifetime of certificates.
    a ← peras A
    -- Fetch the current round.
    round ← use currentRound
    -- Fetch the latest certificate and the latest on the chain.
    certPrime ← use latestCertSeen
    certStar ← use latestCertOnChain
    -- Check whether a certificate exists from two rounds past.
    penultimate ←
      use certs                                     -- Fetch the certificates.
        ⇉ takeWhile (noMoreThanTwoRoundsOld round)  -- For efficiency, since the list is sorted by decreasing round.
        ⇉ any (twoRoundsOld round)                  -- Check if any certificates are two rounds old.
    -- Check that the latest certificate has not expired.
    unexpired ← pure $ round <= certificateRound certPrime + a
    -- Check that the latest certificate is newer than the latest on the chain.
    newer ← pure $ certificateRound certPrime > certificateRound certStar
    -- Determine whether the latest certificate should be included in the new block.
    cert ← pure (
             if not penultimate && unexpired && newer
               then Just certPrime
               else Nothing
           )
    -- Forge the block.
    block ← signBlock <$> use currentSlot <*> use creatorId <*> pure parent <*> pure cert <*> pure txs
    -- Extend the preferred chain.
    chain ← use preferredChain ⇉ extendChain block
    -- Diffuse the new chain.
    diffuse ↞ NewChain chain
  where
    -- Check whether a certificate is no more than two rounds old.
    noMoreThanTwoRoundsOld : Round → Certificate → Bool
    noMoreThanTwoRoundsOld round cert = certificateRound cert + 2 <= round
    -- Check whether a certificate is exactly two rounds old.
    twoRoundsOld : Round → Certificate → Bool
    twoRoundsOld round cert = certificateRound cert + 2 == round
{-# COMPILE AGDA2HS blockCreation #-}

-- Select a block to vote for, using preagreement.
preagreement : NodeState (Maybe Block)
preagreement =
  do
    l ← peras L
    now ← use currentSlot
    -- FIXME: To be implemented.
    pure Nothing
{-# COMPILE AGDA2HS preagreement #-}

-- Vote.
voting : NodeOperation
voting =
  do
    -- Check for a preagreement block.
    agreed ← preagreement
    case agreed of λ where
      -- There was no preagreement block.
      Nothing →
        do
          -- No messages if preagreement does not yield a block.
          diffuse
      -- There was a preagreement block.
      (Just block) →
        do
          -- Fetch the current slot and round.
          now ← use currentSlot
          round ← use currentRound
          -- Fetch the chain-ignorance period.
          r ← peras R
          -- Fetch the cool-down duration.
          k <- peras K
          -- Check whether the latest certificate is from the previous round.
          vr1a ←
            use latestCertSeen     -- Fetch the latest certificate.
              ⇉ oneRoundOld round  -- Check whether that is from the previous round.
          -- Check whether the block ends the chain indicated by the latest certificate.
          vr1b ←
            use latestCertSeen    -- Fetch the latest certificate.
              ⇉ certificateBlock  -- Find which block it certified.
              ⇉ extendedBy block  -- Check whether the block under consideration extends the certified block.
          -- Check whether the certificate is in the chain-ignorance period.
          vr2a ←
            use latestCertSeen            -- Fetch the latest certificate.
              ⇉ inChainIgnorance round r  -- Check whether the certificate falls in the chain-ignorance period.
          -- Check whether the cool-down period has ended.
          vr2b ←
            use latestCertOnChain  -- Fetch the latest certificate on the preferred chain.
              ⇉ afterCooldown round k
          -- Determine whether to vote.
          if (vr1a && vr1b || vr2a && vr2b)
             then (
               -- Vote.
               do
                 -- Sign the vote.
                 vote ← signVote round <$> use creatorId <*> pure block
                 -- Record the vote.
                 votes ≕ (vote ∷_)
                 -- Diffuse the vote.
                 diffuse ↞ NewVote vote
              )
             else (
               -- Do not vote.
               do
                 -- No message because no vote was cast.
                 diffuse
             )
  where
    afterSlot : Slot → ℕ → Block → Bool
    afterSlot s l block = slot block + l > s
    hashOfFirstBlock : List Block → Hash Block
    hashOfFirstBlock [] = genesisHash
    hashOfFirstBlock (block ∷ _) = hash iBlockHashable block
    oneRoundOld : Round → Certificate → Bool
    oneRoundOld round cert = certificateRound cert + 1 == round
    extendedBy : Block → Hash Block → Bool
    extendedBy block blockHash =
      -- FIXME: To be implemented.
      _
    inChainIgnorance : Round → ℕ → Certificate → Bool
    inChainIgnorance round r cert = round >= certificateRound cert + r
    afterCooldown : Round → ℕ → Certificate → Bool
    afterCooldown round k cert =
      -- FIXME: To be implemented.
      _
{-# COMPILE AGDA2HS voting #-}
