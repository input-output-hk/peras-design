{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fno-warn-missing-pattern-synonym-signatures #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module Peras.Conformance.Model where

import Control.Monad (guard)
import Numeric.Natural (Natural)
import Peras.Block (Block (MkBlock, bodyHash, certificate, creatorId, leadershipProof, parentBlock, signature, slotNumber), Certificate (MkCertificate, blockRef, round), PartyId, tipHash)
import Peras.Chain (Chain, Vote (MkVote, blockHash, votingRound), insertCert, lastSlot)
import Peras.Conformance.Params (PerasParams (MkPerasParams, perasA, perasB, perasK, perasL, perasR, perasU, perasτ), defaultPerasParams)
import Peras.Crypto (Hash (MkHash), Hashable (hash), emptyBS)
import Peras.Foreign (checkLeadershipProof, checkSignedBlock, checkSignedVote, createLeadershipProof, createMembershipProof, createSignedBlock, createSignedVote, mkParty)
import Peras.Numbering (RoundNumber (getRoundNumber), SlotNumber (getSlotNumber), nextRound, nextSlot, slotInRound, slotToRound)
import Peras.Util (comparing, decP, decS, eqDec, ge, gt, isYes, mapMaybe, maximumBy, maybeToList)

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
  | BadChain Chain
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

chainExtends :: Hash Block -> Certificate -> Chain -> Bool
chainExtends h c =
  any (\block -> hash block == blockRef c)
    . dropWhile (\block' -> hash block' /= h)

extends :: Hash Block -> Certificate -> [Chain] -> Bool
extends h cert chain =
  if cert == genesisCert
    then True
    else any (chainExtends h cert) chain

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

addChain' :: NodeModel -> Chain -> NodeModel
addChain' s c =
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

(===) :: RoundNumber -> RoundNumber -> Bool
x === y = x == y

vr1A :: NodeModel -> Bool
vr1A s = rFromSlot s === nextRound (round (cert' s))

vr1B' :: NodeModel -> Bool
vr1B' s = extends (votingBlockHash s) (cert' s) (allChains s)

extendsDec :: Hash Block -> Certificate -> [Chain] -> Bool
extendsDec h c ch = extends h c ch

vr1B :: NodeModel -> Bool
vr1B s = extendsDec (votingBlockHash s) (cert' s) (allChains s)

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
    ( eqDec
        ( mod
            (fromIntegral (getRoundNumber (rFromSlot s)))
            (fromIntegral (perasK (protocol s)))
        )
        ( mod
            (fromIntegral (getRoundNumber (round (certS s))))
            (fromIntegral (perasK (protocol s)))
        )
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

type SutIsVoter = RoundNumber -> Bool

voteInState :: SutIsVoter -> NodeModel -> Maybe Vote
voteInState sutIsVoter s =
  do
    guard (sutIsVoter (rFromSlot s))
    guard (slotInRound (protocol s) (clock s) == 0)
    makeVote' s

votesInState :: SutIsVoter -> NodeModel -> [Vote]
votesInState sutIsVoter = maybeToList . voteInState sutIsVoter

type SutIsSlotLeader = SlotNumber -> Bool

chainInState :: SutIsSlotLeader -> NodeModel -> Maybe Chain
chainInState sutIsSlotLeader s =
  do
    guard (sutIsSlotLeader (clock s))
    guard (slotNumber block == clock s)
    guard (checkBlockFromSut block)
    guard (parentBlock block == tipHash rest)
    guard (rest == pref s)
    guard (checkSignedBlock block)
    guard (checkLeadershipProof (leadershipProof block))
    guard (lastSlot rest < slotNumber block)
    guard (bodyHash block == hash [])
    pure (block : rest)
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
      (tipHash rest)
      (if includeCert' then Just (cert' s) else Nothing)
      (createLeadershipProof (clock s) [mkParty sutId [] []])
      (MkHash emptyBS)

chainsInState :: SutIsSlotLeader -> NodeModel -> [Chain]
chainsInState sutIsSlotLeader =
  maybeToList . chainInState sutIsSlotLeader

needCert' :: NodeModel -> Bool
needCert' s =
  not
    ( any
        ( \c ->
            getRoundNumber (round c) + 2
              == getRoundNumber (slotToRound (protocol s) (clock s))
        )
        (allSeenCerts s)
    )
    && getRoundNumber (slotToRound (protocol s) (clock s))
      <= perasA (protocol s) + getRoundNumber (round (cert' s))
    && getRoundNumber (round (certS s))
      <= getRoundNumber (round (cert' s))

transition ::
  (SutIsSlotLeader, SutIsVoter) ->
  NodeModel ->
  EnvAction ->
  Maybe (([Chain], [Vote]), NodeModel)
transition (sutIsSlotLeader, sutIsVoter) s Tick =
  Just
    (
      ( chainsInState
          sutIsSlotLeader
          ( NodeModel
              (nextSlot (clock s))
              (protocol s)
              (allChains s)
              (allVotes s)
              (allSeenCerts s)
          )
      , votesInState
          sutIsVoter
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
            sutIsSlotLeader
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
            sutIsVoter
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
                        sutIsSlotLeader
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
                        sutIsVoter
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
transition _ _ (NewChain []) = Nothing
transition
  _
  s
  ( NewChain
      ( MkBlock
          slotNumber
          creatorId
          parentBlock
          Nothing
          leadershipProof
          signature
          bodyHash
          : rest
        )
    ) =
    do
      guard (not $ needCert' s)
      guard (slotNumber == clock s)
      guard
        ( checkBlockFromOther
            ( MkBlock
                slotNumber
                creatorId
                parentBlock
                Nothing
                leadershipProof
                signature
                bodyHash
            )
        )
      guard (parentBlock == tipHash rest)
      guard (rest == pref s)
      guard
        ( checkSignedBlock
            ( MkBlock
                slotNumber
                creatorId
                parentBlock
                Nothing
                leadershipProof
                signature
                bodyHash
            )
        )
      guard (checkLeadershipProof leadershipProof)
      guard (lastSlot rest < slotNumber)
      guard (bodyHash == hash [])
      Just
        ( ([], [])
        , NodeModel
            (clock s)
            (protocol s)
            ( ( MkBlock
                  slotNumber
                  creatorId
                  parentBlock
                  Nothing
                  leadershipProof
                  signature
                  bodyHash
                  : rest
              )
                : allChains s
            )
            (allVotes s)
            ( foldr
                insertCert
                (allSeenCerts s)
                ( mapMaybe
                    (\r -> certificate r)
                    ( MkBlock
                        slotNumber
                        creatorId
                        parentBlock
                        Nothing
                        leadershipProof
                        signature
                        bodyHash
                        : rest
                    )
                )
            )
        )
transition
  _
  s
  ( NewChain
      ( MkBlock
          slotNumber
          creatorId
          parentBlock
          (Just cert)
          leadershipProof
          signature
          bodyHash
          : rest
        )
    ) =
    do
      guard (needCert' s)
      guard (cert == cert' s)
      guard (slotNumber == clock s)
      guard
        ( checkBlockFromOther
            ( MkBlock
                slotNumber
                creatorId
                parentBlock
                (Just cert)
                leadershipProof
                signature
                bodyHash
            )
        )
      guard (parentBlock == tipHash rest)
      guard (rest == pref s)
      guard
        ( checkSignedBlock
            ( MkBlock
                slotNumber
                creatorId
                parentBlock
                (Just cert)
                leadershipProof
                signature
                bodyHash
            )
        )
      guard (checkLeadershipProof leadershipProof)
      guard (lastSlot rest < slotNumber)
      guard (bodyHash == hash [])
      Just
        ( ([], [])
        , NodeModel
            (clock s)
            (protocol s)
            ( ( MkBlock
                  slotNumber
                  creatorId
                  parentBlock
                  (Just cert)
                  leadershipProof
                  signature
                  bodyHash
                  : rest
              )
                : allChains s
            )
            (allVotes s)
            ( foldr
                insertCert
                (allSeenCerts s)
                ( mapMaybe
                    (\r -> certificate r)
                    ( MkBlock
                        slotNumber
                        creatorId
                        parentBlock
                        (Just cert)
                        leadershipProof
                        signature
                        bodyHash
                        : rest
                    )
                )
            )
        )
transition _ s (NewVote v) =
  do
    guard (slotInRound (protocol s) (clock s) == 0)
    guard (slotToRound (protocol s) (clock s) == votingRound v)
    guard (checkSignedVote v)
    guard (checkVoteFromOther v)
    guard (isYes $ checkVotingRules s)
    guard (votingBlockHash s == blockHash v)
    Just (([], []), addVote' s v)
transition _ s (BadChain blocks) =
  do
    guard
      ( any
          (\block -> hasForged (slotNumber block) (creatorId block))
          blocks
      )
    Just (([], []), s)
 where
  equivocatedBlock :: SlotNumber -> PartyId -> Block -> Bool
  equivocatedBlock slot pid block =
    slot == slotNumber block && pid == creatorId block
  hasForged :: SlotNumber -> PartyId -> Bool
  hasForged slot pid =
    any (any $ equivocatedBlock slot pid) $ allChains s
transition _ s (BadVote v) =
  do
    guard (hasVoted (voterId v) (votingRound v) s)
    Just (([], []), s)
