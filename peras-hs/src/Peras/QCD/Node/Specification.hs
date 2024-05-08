module Peras.QCD.Node.Specification where

import Numeric.Natural (Natural)
import Peras.QCD.Crypto (Hash, Hashable (hash))
import Peras.QCD.Crypto.Placeholders (buildCertificate)
import Peras.QCD.Node.Model (NodeModel, NodeModification, NodeOperation, certs, chains, creatorId, currentSlot, diffuse, latestCertOnChain, latestCertSeen, peras, preferredChain, protocol, votes)
import Peras.QCD.Protocol (ParamSymbol (B), Params, τ)
import Peras.QCD.State (State, use, (≔), (≕))
import Peras.QCD.Types (Block (parent, slot), Certificate (certificateBlock, certificateRound), Chain (ChainBlock, Genesis), PartyId, Round, Slot, Vote (voteRound), certsOnChain, chainBlocks, genesisCert, genesisHash, lastCert)
import Peras.QCD.Util (addOne, count, eqBy, firstWithDefault, groupBy, unionDescending, (⇉))

import Peras.QCD.Types.Instances ()

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
