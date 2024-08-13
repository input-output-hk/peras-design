{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-name-shadowing -Wno-unused-matches #-}

module Peras.Conformance.Model where

import Control.Monad (guard)
import Data.Maybe (mapMaybe)
import Numeric.Natural (Natural)
import Peras.Block (Block (MkBlock, certificate, creatorId, signature, slotNumber), Certificate (MkCertificate, blockRef, round), PartyId)
import Peras.Chain (Chain, Vote (MkVote, blockHash, votingRound))
import Peras.Conformance.Params (PerasParams (MkPerasParams, perasA, perasB, perasK, perasL, perasR, perasT, perasU, perasτ), defaultPerasParams)
import Peras.Crypto (Hash (MkHash), Hashable (hash), emptyBS)
import Peras.Foreign (checkSignedVote, createMembershipProof, createSignedVote, mkParty)
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
        0
    )
    [genesisChain]
    []
    [genesisCert]

blockOldEnough :: PerasParams -> SlotNumber -> Block -> Bool
blockOldEnough params clock (MkBlock slot _ _ _ _ _ _) =
  getSlotNumber slot + perasL params + perasT params
    <= getSlotNumber clock

chainExtends :: Block -> Certificate -> Chain -> Bool
chainExtends b c =
  any (\block -> hash block == blockRef c)
    . dropWhile (\block' -> hash block' /= hash b)

extends :: Block -> Certificate -> [Chain] -> Bool
extends block cert chains = any (chainExtends block cert) chains

headMaybe :: [a] -> Maybe a
headMaybe [] = Nothing
headMaybe (x : _) = Just x

votingBlock :: NodeModel -> Maybe Block
votingBlock s =
  headMaybe
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
    (allSeenCerts s)

addVote' :: NodeModel -> Vote -> NodeModel
addVote' s v =
  NodeModel
    (clock s)
    (protocol s)
    (allChains s)
    (v : allVotes s)
    (allSeenCerts s)

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
vr1B' s =
  case votingBlock s of
    Nothing -> False
    Just block -> extends block (cert' s) (allChains s)

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

makeVote' :: NodeModel -> Maybe Vote
makeVote' s =
  do
    guard (isYes $ checkVotingRules s)
    block <- votingBlock s
    pure $ makeVote (protocol s) (clock s) block

votesInState :: NodeModel -> [Vote]
votesInState s =
  maybeToList
    ( do
        guard (slotInRound (protocol s) (clock s) == 0)
        makeVote' s
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

checkVoteFromSut :: Vote -> Bool
checkVoteFromSut (MkVote _ c _ _ _) = c == sutId

checkVoteNotFromSut :: Vote -> Bool
checkVoteNotFromSut = not . checkVoteFromSut

checkBlockFromSut :: Block -> Bool
checkBlockFromSut (MkBlock _ c _ _ _ _ _) = c == sutId

checkBlockNotFromSut :: Block -> Bool
checkBlockNotFromSut = not . checkBlockFromSut

hashMaybeBlock :: Maybe Block -> Hash Block
hashMaybeBlock (Just b) = hash b
hashMaybeBlock Nothing = genesisHash

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
            (mapMaybe (\r -> certificate r) chain)
        )
    )
transition s (NewVote v) =
  do
    guard (slotInRound (protocol s) (clock s) == 0)
    guard (checkSignedVote v)
    guard (checkVoteNotFromSut v)
    guard (isYes $ checkVotingRules s)
    guard (hashMaybeBlock (votingBlock s) == blockHash v)
    Just ([], addVote' s v)
