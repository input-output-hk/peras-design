{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-name-shadowing -Wno-unused-matches #-}

module Peras.Conformance.Model where

import Control.Monad (guard)
import Numeric.Natural (Natural)
import Peras.Block (Block (MkBlock, creatorId, signature, slotNumber), Certificate (MkCertificate, blockRef, round), PartyId)
import Peras.Chain (Chain, Vote (blockHash, votingRound))
import Peras.Conformance.Params (
  PerasParams (
    MkPerasParams,
    perasA,
    perasB,
    perasK,
    perasL,
    perasR,
    perasU,
    perasτ
  ),
  defaultPerasParams,
 )
import Peras.Crypto (Hash (MkHash), Hashable (hash), emptyBS)
import Peras.Foreign (checkSignedVote, createMembershipProof, createSignedVote, mkParty)
import Peras.Numbering (RoundNumber (getRoundNumber), SlotNumber (getSlotNumber), nextRound, nextSlot, slotInRound, slotToRound)
import Peras.Util (catMaybes, comparing, listToMaybe, maximumBy, maybeToList)
import qualified Prelude ((/=))

import Control.Monad.Identity
import Data.Function (on)
import Data.Set (Set)
import qualified Data.Set as Set
import Peras.Block (blockRef, certificate)
import Peras.Crypto (hash)
import Peras.Orphans ()
import Prelude hiding (round)

intToInteger :: Int -> Integer
intToInteger = fromIntegral

data NodeModel = NodeModel
  { clock :: SlotNumber
  , protocol :: PerasParams
  , allChains :: [Chain]
  , allVotes :: [Vote]
  , allSeenCerts :: [Certificate]
  }
  deriving (Eq, Show)

data EnvAction
  = Tick
  | NewChain Chain
  | NewVote Vote
  deriving (Eq, Show)

genesisHash :: Hash Block
genesisHash = MkHash emptyBS

genesisChain :: Chain
genesisChain = []

genesisCert :: Certificate
genesisCert = MkCertificate 0 genesisHash

initialModelState :: NodeModel
initialModelState =
  NodeModel
    1
    ( MkPerasParams
        5
        (perasA defaultPerasParams)
        1
        1
        1
        1
        (perasB defaultPerasParams)
        0
    )
    [genesisChain]
    []
    [genesisCert]

sutId :: PartyId
sutId = 1

insertCert :: Certificate -> [Certificate] -> [Certificate]
insertCert cert [] = [cert]
insertCert cert (cert' : certs) =
  if cert == cert'
    then cert' : certs
    else cert' : insertCert cert certs

seenBeforeStartOfRound ::
  PerasParams -> RoundNumber -> (Certificate, SlotNumber) -> Bool
seenBeforeStartOfRound params r (c, s) =
  getSlotNumber s <= getRoundNumber r * perasU params

chainWeight :: Natural -> [Certificate] -> Chain -> Natural
chainWeight boost certs = chainWeight' 0
 where
  isCertified :: Block -> Bool
  isCertified block =
    any (\cert -> hash block == blockRef cert) certs
  chainWeight' :: Natural -> [Block] -> Natural
  chainWeight' accum [] = accum
  chainWeight' accum (block : blocks) =
    if isCertified block
      then chainWeight' (accum + 1 + boost) blocks
      else chainWeight' (accum + 1) blocks

compareTip :: Chain -> Chain -> Ordering
compareTip [] [] = EQ
compareTip [] _ = LT
compareTip _ [] = GT
compareTip (block1 : blocks1) (block2 : blocks2) =
  case compare (slotNumber block1) (slotNumber block2) of
    EQ -> case compare (creatorId block1) (creatorId block2) of
      EQ -> compare (signature block1) (signature block2)
      y -> y
    x -> x

compareChains ::
  Natural -> [Certificate] -> Chain -> Chain -> Ordering
compareChains boost certs chain1 chain2 =
  case compare
    (chainWeight boost certs chain1)
    (chainWeight boost certs chain2) of
    EQ -> compareTip chain1 chain2
    x -> x

preferredChain :: PerasParams -> [Certificate] -> [Chain] -> Chain
preferredChain params certs =
  maximumBy
    genesisChain
    (compareChains (fromIntegral (perasB params)) certs)

makeVote :: PerasParams -> SlotNumber -> Block -> Vote
makeVote params slot block =
  createSignedVote
    (mkParty 1 [] [slotToRound params slot])
    (slotToRound params slot)
    (hash block)
    ( createMembershipProof
        (slotToRound params slot)
        [mkParty 1 [] [slotToRound params slot]]
    )
    1

blockOldEnough :: PerasParams -> SlotNumber -> Block -> Bool
blockOldEnough params clock (MkBlock slot _ _ _ _ _ _) =
  getSlotNumber slot + perasL params <= getSlotNumber clock

extends :: Block -> Certificate -> [Chain] -> Bool
extends block cert chain =
  (cert == genesisCert) || any chainExtends chain
 where
  chainExtends :: Chain -> Bool
  chainExtends =
    any (\block -> hash block == blockRef cert)
      . dropWhile (\block' -> (Prelude./=) (hash block') (hash block))

makeVote' :: NodeModel -> Maybe Vote
makeVote' s =
  do
    block <-
      listToMaybe
        (dropWhile (not . blockOldEnough params slot) pref)
    guard (vr1A && vr1B block || vr2A && vr2B)
    pure $ makeVote params slot block
 where
  params :: PerasParams
  params = protocol s
  slot :: SlotNumber
  slot = clock s
  r :: RoundNumber
  r = slotToRound params slot
  pref :: Chain
  pref = preferredChain params (allSeenCerts s) (allChains s)
  cert' :: Certificate
  cert' =
    maximumBy
      genesisCert
      (comparing (\r -> round r))
      (allSeenCerts s)
  certS :: Certificate
  certS =
    maximumBy
      genesisCert
      (comparing (\r -> round r))
      (catMaybes (map certificate pref))
  vr1A :: Bool
  vr1A = nextRound (round cert') == r
  vr1B :: Block -> Bool
  vr1B block = extends block cert' (allChains s)
  vr2A :: Bool
  vr2A =
    getRoundNumber r >= getRoundNumber (round cert') + perasR params
  vr2B :: Bool
  vr2B =
    r > round certS
      && mod (getRoundNumber r) (perasK params)
        == mod (getRoundNumber (round certS)) (perasK params)

makeVote'' :: NodeModel -> Maybe Bool
makeVote'' = pure . maybe False (const True) . makeVote'

votesInState :: NodeModel -> [Vote]
votesInState s =
  maybeToList
    ( do
        guard (slotInRound params slot == 0)
        makeVote' s
    )
 where
  params :: PerasParams
  params = protocol s
  slot :: SlotNumber
  slot = clock s

newQuora :: Natural -> [Certificate] -> [Vote] -> [Certificate]
newQuora _ _ [] = []
newQuora quorum priorCerts (vote : votes) =
  if not
    ( any
        ( \cert ->
            votingRound vote == round cert && blockHash vote == blockRef cert
        )
        priorCerts
    )
    && intToInteger
      ( length
          ( filter
              ( \vote' ->
                  votingRound vote == votingRound vote'
                    && blockHash vote == blockHash vote'
              )
              votes
          )
          + 1
      )
      >= fromIntegral quorum
    then
      MkCertificate (votingRound vote) (blockHash vote)
        : newQuora
          quorum
          (MkCertificate (votingRound vote) (blockHash vote) : priorCerts)
          ( filter
              ( not
                  . \vote' ->
                    votingRound vote == votingRound vote'
                      && blockHash vote == blockHash vote'
              )
              votes
          )
    else
      newQuora
        quorum
        priorCerts
        ( filter
            ( not
                . \vote' ->
                  votingRound vote == votingRound vote'
                    && blockHash vote == blockHash vote'
            )
            votes
        )

transition :: NodeModel -> EnvAction -> Maybe ([Vote], NodeModel)
transition s Tick =
  Just
    ( sutVotes
    , NodeModel
        (clock s')
        (protocol s')
        (allChains s')
        (sutVotes ++ allVotes s')
        (foldr insertCert (allSeenCerts s') certsFromQuorum)
    )
 where
  s' :: NodeModel
  s' =
    NodeModel
      (nextSlot (clock s))
      (protocol s)
      (allChains s)
      (allVotes s)
      (allSeenCerts s)
  sutVotes :: [Vote]
  sutVotes = votesInState s'
  certsFromQuorum :: [Certificate]
  certsFromQuorum =
    newQuora
      (fromIntegral (perasτ (protocol s)))
      (allSeenCerts s)
      (allVotes s)
transition s (NewChain chain) =
  Just
    ( []
    , NodeModel
        (clock s)
        (protocol s)
        (chain : allChains s)
        (allVotes s)
        ( foldr
            insertCert
            (allSeenCerts s)
            (catMaybes $ map certificate chain)
        )
    )
transition s (NewVote v) =
  do
    guard (slotInRound (protocol s) (clock s) == 0)
    guard (checkSignedVote v)
    checkVotingRules <- makeVote'' s
    guard checkVotingRules
    Just
      ( []
      , NodeModel
          (clock s)
          (protocol s)
          (allChains s)
          (v : allVotes s)
          (allSeenCerts s)
      )
