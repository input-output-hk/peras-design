module Peras.Abstract.Protocol.Model where

import Peras.Abstract.Protocol.Params (PerasParams(MkPerasParams, perasA, perasB, perasU), defaultPerasParams)
import Peras.Block (Block, Certificate(MkCertificate))
import Peras.Chain (Chain, Vote)
import Peras.Crypto (Hash(MkHash), replicateBS)
import Peras.Numbering (RoundNumber(MkRoundNumber), SlotNumber(MkSlotNumber))

import Peras.Orphans
import Peras.Block (certificate)

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

slotToRound :: PerasParams -> SlotNumber -> RoundNumber
slotToRound protocol (MkSlotNumber n)
  = MkRoundNumber (div n (perasU protocol))

nextSlot :: SlotNumber -> SlotNumber
nextSlot (MkSlotNumber n) = MkSlotNumber (1 + n)

insertCert ::
           SlotNumber ->
             Maybe Certificate ->
               [(Certificate, SlotNumber)] -> [(Certificate, SlotNumber)]
insertCert slot Nothing certs = certs
insertCert slot (Just cert) [] = [(cert, slot)]
insertCert slot (Just cert) ((cert', slot') : certs)
  = if cert == cert' then (cert', slot') : certs else
      (cert', slot') : insertCert slot (Just cert) certs

transition :: NodeModel -> EnvAction -> Maybe ([Vote], NodeModel)
transition s Tick = Nothing
transition s (NewChain chain)
  = Just
      ([],
       NodeModel (clock s) (protocol s)
         ((slotToRound (protocol s) (clock s), chain) : allChains s)
         (allVotes s)
         (foldr (insertCert (nextSlot (clock s)) . certificate)
            (allSeenCerts s)
            chain))
transition s (NewVote v)
  = Just
      ([],
       NodeModel (clock s) (protocol s) (allChains s) (v : allVotes s)
         (allSeenCerts s))

