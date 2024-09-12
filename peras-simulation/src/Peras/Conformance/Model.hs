{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-name-shadowing -Wno-unused-matches #-}

module Peras.Conformance.Model where

import Control.Monad (guard)
import Data.Maybe (mapMaybe)
import Numeric.Natural (Natural)
import Peras.Block (Block (MkBlock, certificate, creatorId, leadershipProof, parentBlock, signature, slotNumber), Certificate (MkCertificate, blockRef, round), PartyId, tipHash)
import Peras.Chain (Chain, Vote (MkVote, blockHash, votingRound), insertCert)
import Peras.Conformance.Params (PerasParams (MkPerasParams, perasA, perasB, perasK, perasL, perasR, perasT, perasU, perasτ), defaultPerasParams)
import Peras.Crypto (Hash (MkHash), Hashable (hash), emptyBS)
import Peras.Foreign (checkLeadershipProof, checkSignedBlock, checkSignedVote, createLeadershipProof, createMembershipProof, createSignedBlock, createSignedVote, mkParty)
import Peras.Numbering (RoundNumber (getRoundNumber), SlotNumber (getSlotNumber), nextRound, nextSlot, slotInRound, slotToRound)
import Peras.Util (comparing, maximumBy, maybeToList)

import Control.Monad.Identity
import Data.Function (on)
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Integer
import Peras.Crypto (hash)
import Peras.Orphans ()
import Prelude hiding (round)

intToInteger :: Int -> Integer
intToInteger = fromIntegral

voterId :: Vote -> PartyId
voterId (MkVote _ p _ _ _) = p

data EnvAction
  = Tick
  | NewChain Chain
  | NewVote Vote
  | BadVote Vote
  deriving (Eq, Show)

genesisHash :: Hash Block
genesisHash = MkHash emptyBS

genesisChain :: Chain
genesisChain = []

genesisCert :: Certificate
genesisCert = MkCertificate 0 genesisHash

sutId :: PartyId
sutId = 1

otherId :: PartyId
otherId = 2

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

makeVote :: PerasParams -> SlotNumber -> Hash Block -> Vote
makeVote params slot h =
  createSignedVote
    (mkParty sutId [] [slotToRound params slot])
    (slotToRound params slot)
    h
    ( createMembershipProof
        (slotToRound params slot)
        [mkParty sutId [] [slotToRound params slot]]
    )
    1

data NodeModel = NodeModel
  { clock :: SlotNumber
  , protocol :: PerasParams
  , allChains :: [Chain]
  , allVotes :: [Vote]
  , allSeenCerts :: [Certificate]
  }
  deriving (Eq, Show)

rFromSlot :: NodeModel -> RoundNumber
rFromSlot s = slotToRound (protocol s) (clock s)

cert' :: NodeModel -> Certificate
cert' s =
  maximumBy
    genesisCert
    (comparing (\r -> round r))
    (allSeenCerts s)

pref :: NodeModel -> Chain
pref s = preferredChain (protocol s) (allSeenCerts s) (allChains s)

certS :: NodeModel -> Certificate
certS s =
  maximumBy
    genesisCert
    (comparing (\r -> round r))
    (mapMaybe (\r -> certificate r) (pref s))

testParams :: PerasParams
testParams =
  MkPerasParams
    5
    (perasA defaultPerasParams)
    1
    1
    1
    1
    (perasB defaultPerasParams)
    0
    0

initialModelState :: NodeModel
initialModelState =
  NodeModel 1 testParams [genesisChain] [] [genesisCert]

blockOldEnough :: PerasParams -> SlotNumber -> Block -> Bool
blockOldEnough params clock (MkBlock slot _ _ _ _ _ _) =
  getSlotNumber slot + perasL params + perasT params
    <= getSlotNumber clock

chainExtends :: Hash Block -> Certificate -> Chain -> Bool
chainExtends h c =
  any (\block -> hash block == blockRef c)
    . dropWhile (\block' -> hash block' /= h)

extends :: Hash Block -> Certificate -> [Chain] -> Bool
extends h cert = any (chainExtends h cert)

votingBlockHash :: NodeModel -> Hash Block
votingBlockHash s =
  tipHash
    . filter
      ( \case
          b ->
            getSlotNumber (slotNumber b) + perasL (protocol s)
              <= getSlotNumber (clock s)
      )
    $ pref s

newChain' :: NodeModel -> Chain -> NodeModel
newChain' s c =
  NodeModel
    (clock s)
    (protocol s)
    (c : allChains s)
    (allVotes s)
    ( foldr
        insertCert
        (allSeenCerts s)
        (mapMaybe (\r -> certificate r) c)
    )

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

certsFromQuorum :: NodeModel -> [Certificate]
certsFromQuorum s =
  newQuora
    (fromIntegral (perasτ (protocol s)))
    (allSeenCerts s)
    (allVotes s)

addVote' :: NodeModel -> Vote -> NodeModel
addVote' s v =
  NodeModel
    (clock s)
    (protocol s)
    (allChains s)
    (v : allVotes s)
    ( foldr
        insertCert
        (allSeenCerts s)
        ( certsFromQuorum
            ( NodeModel
                (clock s)
                (protocol s)
                (allChains s)
                (v : allVotes s)
                (allSeenCerts s)
            )
        )
    )

hasVoted :: PartyId -> RoundNumber -> NodeModel -> Bool
hasVoted p r s =
  any (\v -> p == voterId v && r == votingRound v) (allVotes s)

isYes :: Bool -> Bool
isYes True = True
isYes False = False

decP :: Bool -> Bool -> Bool
decP va vb = va && vb

decS :: Bool -> Bool -> Bool
decS va vb = va || vb

(===) :: RoundNumber -> RoundNumber -> Bool
x === y = x == y

eq :: Integer -> Integer -> Bool
eq = (==)

gt :: Integer -> Integer -> Bool
gt = gtInteger

ge :: Integer -> Integer -> Bool
ge = geInteger

vr1A :: NodeModel -> Bool
vr1A s = nextRound (round (cert' s)) === rFromSlot s

vr1B' :: NodeModel -> Bool
vr1B' s = extends (votingBlockHash s) (cert' s) (allChains s)

vr1B :: NodeModel -> Bool
vr1B s = vr1B' s

vr2A :: NodeModel -> Bool
vr2A s =
  ge
    (getRoundNumber (rFromSlot s))
    (getRoundNumber (round (cert' s)) + perasR (protocol s))

vr2B :: NodeModel -> Bool
vr2B s =
  decP
    ( gt
        (getRoundNumber (rFromSlot s))
        (getRoundNumber (round (certS s)))
    )
    ( eq
        (mod (getRoundNumber (rFromSlot s)) (perasK (protocol s)))
        (mod (getRoundNumber (round (certS s))) (perasK (protocol s)))
    )

checkVotingRules :: NodeModel -> Bool
checkVotingRules s =
  decS (decP (vr1A s) (vr1B s)) (decP (vr2A s) (vr2B s))

checkVoteFromSut :: Vote -> Bool
checkVoteFromSut (MkVote _ c _ _ _) = c == sutId

checkVoteNotFromSut :: Vote -> Bool
checkVoteNotFromSut = not . checkVoteFromSut

checkVoteFromOther :: Vote -> Bool
checkVoteFromOther (MkVote _ c _ _ _) = c == otherId

checkBlockFromSut :: Block -> Bool
checkBlockFromSut (MkBlock _ c _ _ _ _ _) = c == sutId

checkBlockNotFromSut :: Block -> Bool
checkBlockNotFromSut = not . checkBlockFromSut

checkBlockFromOther :: Block -> Bool
checkBlockFromOther (MkBlock _ c _ _ _ _ _) = c == otherId

makeVote' :: NodeModel -> Maybe Vote
makeVote' s =
  do
    guard (isYes $ checkVotingRules s)
    guard (votingBlockHash s /= genesisHash)
    guard
      ( slotToRound (protocol s) (clock s)
          == votingRound (makeVote (protocol s) (clock s) (votingBlockHash s))
      )
    guard
      ( checkVoteFromSut
          (makeVote (protocol s) (clock s) (votingBlockHash s))
      )
    pure (makeVote (protocol s) (clock s) (votingBlockHash s))

voteInState :: NodeModel -> Maybe Vote
voteInState s =
  do
    guard (slotInRound (protocol s) (clock s) == 0)
    makeVote' s

sutIsSlotLeader :: SlotNumber -> Bool
sutIsSlotLeader n = 1 == mod (getSlotNumber n) 3

votesInState :: NodeModel -> [Vote]
votesInState = maybeToList . voteInState

headBlockHash :: Chain -> Hash Block
headBlockHash [] = genesisHash
headBlockHash (b : _) = hash b

chainsInState :: NodeModel -> [Chain]
chainsInState s =
  if sutIsSlotLeader (clock s) then [block : rest] else []
 where
  rest :: Chain
  rest = pref s
  notPenultimateCert :: Certificate -> Bool
  notPenultimateCert cert =
    getRoundNumber (round cert) + 2 /= getRoundNumber (rFromSlot s)
  noPenultimateCert :: Bool
  noPenultimateCert = all notPenultimateCert (allSeenCerts s)
  unexpiredCert' :: Bool
  unexpiredCert' =
    getRoundNumber (round (cert' s)) + perasA (protocol s)
      >= getRoundNumber (rFromSlot s)
  newerCert' :: Bool
  newerCert' =
    getRoundNumber (round (cert' s))
      > getRoundNumber (round (certS s))
  includeCert' :: Bool
  includeCert' = noPenultimateCert && unexpiredCert' && newerCert'
  block :: Block
  block =
    createSignedBlock
      (mkParty sutId [] [])
      (clock s)
      (headBlockHash rest)
      (if includeCert' then Just (cert' s) else Nothing)
      (createLeadershipProof (clock s) [mkParty sutId [] []])
      (MkHash emptyBS)

transition ::
  NodeModel -> EnvAction -> Maybe (([Chain], [Vote]), NodeModel)
transition s Tick =
  Just
    (
      ( chainsInState
          ( NodeModel
              (nextSlot (clock s))
              (protocol s)
              (allChains s)
              (allVotes s)
              (allSeenCerts s)
          )
      , votesInState
          ( NodeModel
              (nextSlot (clock s))
              (protocol s)
              (allChains s)
              (allVotes s)
              (allSeenCerts s)
          )
      )
    , NodeModel
        (nextSlot (clock s))
        (protocol s)
        ( chainsInState
            ( NodeModel
                (nextSlot (clock s))
                (protocol s)
                (allChains s)
                (allVotes s)
                (allSeenCerts s)
            )
            ++ allChains s
        )
        ( votesInState
            ( NodeModel
                (nextSlot (clock s))
                (protocol s)
                (allChains s)
                (allVotes s)
                (allSeenCerts s)
            )
            ++ allVotes s
        )
        ( foldr
            insertCert
            (allSeenCerts s)
            ( certsFromQuorum
                ( NodeModel
                    (nextSlot (clock s))
                    (protocol s)
                    ( chainsInState
                        ( NodeModel
                            (nextSlot (clock s))
                            (protocol s)
                            (allChains s)
                            (allVotes s)
                            (allSeenCerts s)
                        )
                        ++ allChains s
                    )
                    ( votesInState
                        ( NodeModel
                            (nextSlot (clock s))
                            (protocol s)
                            (allChains s)
                            (allVotes s)
                            (allSeenCerts s)
                        )
                        ++ allVotes s
                    )
                    (allSeenCerts s)
                )
            )
        )
    )
transition _ (NewChain []) = Nothing
transition s (NewChain (block : rest)) =
  do
    guard (slotNumber block == clock s)
    guard (checkBlockFromOther block)
    guard (parentBlock block == headBlockHash rest)
    guard (rest == pref s)
    guard (checkSignedBlock block)
    guard (checkLeadershipProof (leadershipProof block))
    Just
      ( ([], [])
      , NodeModel
          (clock s)
          (protocol s)
          ((block : rest) : allChains s)
          (allVotes s)
          ( foldr
              insertCert
              (allSeenCerts s)
              (mapMaybe (\r -> certificate r) (block : rest))
          )
      )
transition s (NewVote v) =
  do
    guard (slotToRound (protocol s) (clock s) == votingRound v)
    guard (checkSignedVote v)
    guard (checkVoteFromOther v)
    guard (isYes $ checkVotingRules s)
    guard (votingBlockHash s == blockHash v)
    Just (([], []), addVote' s v)
transition s (BadVote v) =
  do
    guard (hasVoted (voterId v) (votingRound v) s)
    Just (([], []), s)
