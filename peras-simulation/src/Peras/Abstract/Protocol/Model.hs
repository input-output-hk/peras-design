{-# LANGUAGE RecordWildCards #-}

module Peras.Abstract.Protocol.Model where

import Control.Monad (guard)
import Peras.Abstract.Protocol.Params (PerasParams(MkPerasParams, perasA, perasB, perasL, perasT, perasU), defaultPerasParams)
import Peras.Block (Block(MkBlock), Certificate(MkCertificate))
import Peras.Chain (Chain, Vote)
import Peras.Crypto (Hash(MkHash), replicateBS)
import Peras.Numbering (RoundNumber(MkRoundNumber, getRoundNumber), SlotNumber(MkSlotNumber, getSlotNumber))

import Peras.Orphans
import Peras.Block (certificate, blockRef)
import Peras.Crypto (hash)
import Data.Maybe (catMaybes, listToMaybe, maybeToList)
import Data.List (maximumBy)
import Data.Function (on)
import qualified Data.Set as Set
import Data.Set (Set)

data NodeModel = NodeModel{clock :: SlotNumber,
                           protocol :: PerasParams, allChains :: [(RoundNumber, Chain)],
                           allVotes :: [Vote], allSeenCerts :: [(Certificate, SlotNumber)]}
                   deriving (Eq, Show)

data EnvAction = Tick
               | NewChain Chain
               | NewVote Vote
                   deriving (Eq, Show)

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

slotInRound :: PerasParams -> SlotNumber -> SlotNumber
slotInRound protocol slot
  = MkSlotNumber (mod (getSlotNumber slot) (perasU protocol))

nextSlot :: SlotNumber -> SlotNumber
nextSlot (MkSlotNumber n) = MkSlotNumber (1 + n)

insertCert ::
           SlotNumber ->
             Certificate ->
               [(Certificate, SlotNumber)] -> [(Certificate, SlotNumber)]
insertCert slot cert [] = [(cert, slot)]
insertCert slot cert ((cert', slot') : certs)
  = if cert == cert' then (cert', slot') : certs else
      (cert', slot') : insertCert slot cert certs

seenBeforeStartOfRound ::
                       PerasParams -> RoundNumber -> (Certificate, SlotNumber) -> Bool
seenBeforeStartOfRound params r (c, s)
  = getSlotNumber s <= getRoundNumber r * perasU params

preferredChain :: PerasParams -> [Certificate] -> [Chain] -> Chain
preferredChain MkPerasParams{..} certs chains =
  maximumBy (compare `on` chainWeight perasB (Set.fromList certs)) (genesisChain : chains)

chainWeight :: Integer -> Set Certificate -> Chain -> Integer
chainWeight boost certs blocks =
  let
    -- Block hashes certified by any certificate.
    certifiedBlocks = Set.map blockRef certs :: Set (Hash Block)
    -- Block hashes on the chain.
    chainBlocks = Set.fromList $ hash <$> blocks :: Set (Hash Block)
   in
    -- Length of the chain plus the boost times the count of certified blocks.
    fromIntegral (length blocks)
      + boost * fromIntegral (Set.size $ certifiedBlocks `Set.intersection` chainBlocks)

makeVote :: RoundNumber -> Block -> Maybe Vote
makeVote r block = do
  let party = mkCommitteeMember (mkParty 1 mempty [0..10000]) protocol (clock - fromIntegral perasT) True
  Right proof <- createMembershipProof r (Set.singleton party)
  Right vote  <- createSignedVote party r (hash block) proof 1
  pure vote

blockOldEnough :: PerasParams -> SlotNumber -> Block -> Bool
blockOldEnough params clock (MkBlock slot _ _ _ _ _ _)
  = getSlotNumber slot + perasL params + perasT params <=
      getSlotNumber clock

votesInState :: NodeModel -> [Vote]
votesInState s
  = maybeToList
      (do guard (slotInRound params slot == MkSlotNumber (perasT params))
          listToMaybe (dropWhile (not . blockOldEnough params slot) pref) >>=
            makeVote r)
  where
    params :: PerasParams
    params = protocol s
    slot :: SlotNumber
    slot = clock s
    r :: RoundNumber
    r = slotToRound params slot
    allChains' :: [Chain]
    allChains'
      = map (\ r -> snd r) $ filter ((< r) . \ r -> fst r) (allChains s)
    allSeenCerts' :: [(Certificate, SlotNumber)]
    allSeenCerts'
      = filter (seenBeforeStartOfRound params r) (allSeenCerts s)
    pref :: Chain
    pref
      = preferredChain params (map (\ r -> fst r) allSeenCerts')
          allChains'

transition :: NodeModel -> EnvAction -> Maybe ([Vote], NodeModel)
transition s Tick
  = Just
      (sutVotes,
       NodeModel (clock s') (protocol s') (allChains s')
         (sutVotes ++ allVotes s')
         (foldr (insertCert (clock s')) (allSeenCerts s') certsFromQuorum))
  where
    s' :: NodeModel
    s'
      = NodeModel (nextSlot (clock s)) (protocol s) (allChains s)
          (allVotes s)
          (allSeenCerts s)
    sutVotes :: [Vote]
    sutVotes = votesInState s'
    certsFromQuorum :: [Certificate]
    certsFromQuorum = []
transition s (NewChain chain)
  = Just
      ([],
       NodeModel (clock s) (protocol s)
         ((slotToRound (protocol s) (clock s), chain) : allChains s)
         (allVotes s)
         (foldr (insertCert (nextSlot (clock s))) (allSeenCerts s)
            (catMaybes $ map certificate chain)))
transition s (NewVote v)
  = Just
      ([],
       NodeModel (clock s) (protocol s) (allChains s) (v : allVotes s)
         (allSeenCerts s))

