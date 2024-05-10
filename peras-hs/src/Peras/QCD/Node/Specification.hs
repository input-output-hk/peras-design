module Peras.QCD.Node.Specification where

import Numeric.Natural (Natural)
import Peras.QCD.Crypto (Hash, Hashable (hash))
import Peras.QCD.Crypto.Placeholders (buildCertificate, signBlock, signVote)
import Peras.QCD.Node.Model (NodeModel, NodeModification, NodeOperation, certs, chains, creatorId, currentRound, currentSlot, diffuse, latestCertOnChain, latestCertSeen, peras, preferredChain, protocol, votes)
import Peras.QCD.Node.Preagreement (preagreement)
import Peras.QCD.Protocol (ParamSymbol (A, B, K, R, U), Params, τ)
import Peras.QCD.State (State, use, (≔), (≕))
import Peras.QCD.Types (Block (parent, slot), Certificate (certificateBlock, certificateRound), Chain (ChainBlock, Genesis), Message (NewChain, NewVote), PartyId, Round, Slot, Tx, Vote (voteRound), certsOnChain, chainBlocks, genesisCert, genesisHash, lastCert)
import Peras.QCD.Util (addOne, count, divideNat, eqBy, firstWithDefault, groupBy, unionDescending, (↞), (⇉))

import Peras.QCD.Types.Instances ()
import Prelude hiding (round)

zero :: Natural
zero = 0

initialize :: Params -> PartyId -> NodeOperation
initialize params party =
  do
    protocol ≔ params
    creatorId ≔ party
    diffuse

chainTip :: Chain -> Hash Block
chainTip Genesis = genesisHash
chainTip (ChainBlock block _) = hash block

extendChain :: Block -> Chain -> Chain
extendChain = ChainBlock

isChainPrefix :: Chain -> Chain -> Bool
isChainPrefix Genesis _ = True
isChainPrefix (ChainBlock block _) chain' =
  test (chainBlocks chain')
 where
  sl :: Slot
  sl = slot block
  hb :: Hash Block
  hb = hash block
  test :: [Block] -> Bool
  test [] = False
  test (b : bs) = hb == parent b || sl < slot b && test bs

updateChains :: [Chain] -> NodeModification
updateChains newChains =
  do
    certs ≕ insertCerts (concatMap certsOnChain newChains)
    chains ≕ filter (not . isPrefixOfAnyChain newChains)
    isPrefixOfOldChains <- use chains ⇉ isPrefixOfAnyChain
    chains ≕ mappend (filter (not . isPrefixOfOldChains) newChains)
 where
  insertCerts :: [Certificate] -> [Certificate] -> [Certificate]
  insertCerts = unionDescending (\r -> certificateRound r)
  isPrefixOfAnyChain :: [Chain] -> Chain -> Bool
  isPrefixOfAnyChain chains' chain =
    any (isChainPrefix chain) chains'

chainWeight :: Natural -> [Certificate] -> Chain -> Natural
chainWeight boost certs' chain =
  count (chainBlocks chain ⇉ hash)
    + boost
      * count
        ( filter
            (flip elem (certs' ⇉ \r -> certificateBlock r))
            (chainBlocks chain ⇉ hash)
        )

heaviestChain :: Natural -> [Certificate] -> [Chain] -> Chain
heaviestChain _ _ [] = Genesis
heaviestChain boost certs' (chain : chains') =
  heaviest (chain, chainWeight boost certs' chain) chains'
 where
  heaviest :: (Chain, Natural) -> [Chain] -> Chain
  heaviest (c, _) [] = c
  heaviest (c, w) (c' : cs) =
    if w <= chainWeight boost certs' c'
      then heaviest (c', chainWeight boost certs' c') cs
      else heaviest (c, w) cs

certificatesForNewQuorums :: State NodeModel [Certificate]
certificatesForNewQuorums =
  do
    tau <- peras τ
    roundsWithCerts <- use certs ⇉ fmap (\r -> certificateRound r)
    ( ( (use votes ⇉ filter (hasNoCertificate roundsWithCerts))
          ⇉ groupByRound
      )
        ⇉ filter (hasQuorum tau)
      )
      ⇉ fmap buildCertificate
 where
  hasNoCertificate :: [Round] -> Vote -> Bool
  hasNoCertificate roundsWithCerts vote =
    notElem (voteRound vote) roundsWithCerts
  groupByRound :: [Vote] -> [[Vote]]
  groupByRound = groupBy (eqBy (\r -> voteRound r))
  hasQuorum :: Natural -> [a] -> Bool
  hasQuorum tau votes' = count votes' >= tau

updateLatestCertSeen :: NodeModification
updateLatestCertSeen =
  (use certs ⇉ firstWithDefault genesisCert) >>= (latestCertSeen ≔)

updateLatestCertOnChain :: NodeModification
updateLatestCertOnChain =
  (use preferredChain ⇉ lastCert) >>= (latestCertOnChain ≔)

fetching :: [Chain] -> [Vote] -> NodeOperation
fetching newChains newVotes =
  do
    currentSlot ≕ addOne
    u <- peras U
    now <- use currentSlot
    currentRound ≔ divideNat now u
    updateChains newChains
    votes ≕ insertVotes newVotes
    newCerts <- certificatesForNewQuorums
    certs ≕ insertCerts newCerts
    boost <- peras B
    heaviest <- heaviestChain boost <$> use certs <*> use chains
    preferredChain ≔ heaviest
    updateLatestCertSeen
    updateLatestCertOnChain
    diffuse
 where
  insertVotes :: [Vote] -> [Vote] -> [Vote]
  insertVotes = unionDescending (\r -> voteRound r)
  insertCerts :: [Certificate] -> [Certificate] -> [Certificate]
  insertCerts = unionDescending (\r -> certificateRound r)

blockCreation :: [Tx] -> NodeOperation
blockCreation txs =
  do
    tip <- use preferredChain ⇉ chainTip
    a <- peras A
    round <- use currentRound
    certPrime <- use latestCertSeen
    certStar <- use latestCertOnChain
    penultimate <-
      ( use certs
          ⇉ takeWhile (noMoreThanTwoRoundsOld round)
        )
        ⇉ any (twoRoundsOld round)
    unexpired <- pure $ round <= certificateRound certPrime + a
    newer <-
      pure $
        certificateRound certPrime > certificateRound certStar
    cert <-
      pure
        ( if not penultimate && unexpired && newer
            then Just certPrime
            else Nothing
        )
    block <-
      signBlock
        <$> use currentSlot
        <*> use creatorId
        <*> pure tip
        <*> pure cert
        <*> pure txs
    chain <- use preferredChain ⇉ extendChain block
    diffuse ↞ NewChain chain
 where
  noMoreThanTwoRoundsOld :: Round -> Certificate -> Bool
  noMoreThanTwoRoundsOld round cert =
    certificateRound cert + 2 <= round
  twoRoundsOld :: Round -> Certificate -> Bool
  twoRoundsOld round cert = certificateRound cert + 2 == round

extends :: Block -> Certificate -> [Chain] -> Bool
extends block cert = any chainExtends . fmap chainBlocks
 where
  dropUntilBlock :: Slot -> Hash Block -> [Block] -> [Block]
  dropUntilBlock slotHint target blocks =
    case dropWhile (\block' -> slotHint < slot block') blocks of
      [] -> []
      candidate : _ ->
        if target == hash candidate
          then dropWhile (\block' -> slotHint < slot block') blocks
          else []
  chainExtends :: [Block] -> Bool
  chainExtends =
    any (\block' -> parent block' == certificateBlock cert)
      . dropUntilBlock (slot block) (hash block)

afterCooldown :: Round -> Natural -> Certificate -> Bool
afterCooldown round k cert = go 1
 where
  go :: Natural -> Bool
  go c =
    case compare round (certificateRound cert + c * k) of
      LT -> False
      EQ -> True
      GT -> go (c + 1)

voting :: NodeOperation
voting =
  do
    agreed <- preagreement
    case agreed of
      Nothing -> diffuse
      Just block -> do
        round <- use currentRound
        r <- peras R
        k <- peras K
        vr1a <- use latestCertSeen ⇉ oneRoundOld round
        vr1b <- extends block <$> use latestCertSeen <*> use chains
        vr2a <- use latestCertSeen ⇉ inChainIgnorance round r
        vr2b <- use latestCertOnChain ⇉ afterCooldown round k
        if vr1a && vr1b || vr2a && vr2b
          then do
            vote <- signVote round <$> use creatorId <*> pure block
            votes ≕ (vote :)
            diffuse ↞ NewVote vote
          else diffuse
 where
  oneRoundOld :: Round -> Certificate -> Bool
  oneRoundOld round cert = certificateRound cert + 1 == round
  inChainIgnorance :: Round -> Natural -> Certificate -> Bool
  inChainIgnorance round r cert = round >= certificateRound cert + r
