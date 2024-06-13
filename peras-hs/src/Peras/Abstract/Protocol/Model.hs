module Peras.Abstract.Protocol.Model where

import Peras.Abstract.Protocol.Params (PerasParams(MkPerasParams, perasA, perasB), defaultPerasParams)
import Peras.Block (Block, Certificate(MkCertificate))
import Peras.Chain (Chain, Vote)
import Peras.Crypto (Hash(MkHash), replicateBS)
import Peras.Numbering (RoundNumber, SlotNumber)

import Peras.Orphans

data NodeModel = NodeModel{clock :: SlotNumber,
                           protocol :: PerasParams, allChains :: [(RoundNumber, Chain)],
                           allVotes :: [Vote], allSeenCerts :: [(Certificate, SlotNumber)]}
                   deriving (Eq, Show)

data EnvAction = Tick
               | NewChain Chain
               | NewVote Vote

genesisHash :: Hash Block
genesisHash = MkHash (replicateBS 8 0)

genesisChain :: Chain
genesisChain = []

genesisCert :: Certificate
genesisCert = MkCertificate 0 genesisHash

initialModelState :: NodeModel
initialModelState
  = NodeModel 1
      (MkPerasParams 5 (perasA defaultPerasParams) 1 1 1 1
         (perasB defaultPerasParams)
         1
         1)
      [(0, genesisChain)]
      []
      [(genesisCert, 0)]

