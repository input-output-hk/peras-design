{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.Conformance.Generators where

import Control.Arrow (Arrow (first, second, (&&&), (***)))
import Control.Monad (filterM)
import Data.Either (fromRight)
import Data.Functor.Identity (Identity (runIdentity))
import Data.List (
  nub,
  partition,
 )
import Data.Maybe (isNothing, mapMaybe)
import qualified Data.Set as Set (singleton)
import GHC.Generics (Generic)
import Peras.Arbitraries ()
import Peras.Block (
  Block (..),
  Certificate (MkCertificate, round),
  PartyId,
 )
import Peras.Chain (Chain, Vote (MkVote, creatorId, votingRound))
import Peras.Conformance.Model (
  EnvAction (NewChain, NewVote, Tick),
  NodeModel (..),
  genesisCert,
  genesisHash,
  otherId,
  sutId,
  transition,
 )
import Peras.Crypto (Hash, Hashable (hash))
import Peras.Numbering (
  RoundNumber (..),
  SlotNumber (..),
  slotInRound,
 )
import Peras.Prototype.Crypto (
  createMembershipProof,
  createSignedBlock,
  createSignedVote,
  mkParty,
 )
import Peras.Prototype.Types (PerasParams (..), hashTip, inRound)
import Test.QuickCheck (
  Arbitrary (arbitrary),
  Gen,
  NonNegative (getNonNegative),
  choose,
  chooseInteger,
  elements,
  frequency,
  sublistOf,
  suchThat,
 )
import Prelude hiding (round)

-- | Constraints on generating Peras values.
data GenConstraints
  = -- | Whether to use consistent and semi-realistic protocol parameters.
    MkGenConstraints
    { -- \^ Don't generate protocol parameters.
      useTestParams :: Bool
    -- ^ Generated parties may not be other than `sutId` and `otherId`.
    , twoParties :: Bool
    -- ^ New blocks are generated at the current slot.
    , blockCurrent :: Bool
    -- ^ New blocks are generated on the preferred (weightiest) chain.
    , blockWeightiest :: Bool
    -- ^ Forbid equivocated blocks.
    , noEquivocatedBlocks :: Bool
    -- ^ Obey the pre-agreement block-selection rule to use the preferred chain.
    , selectionObeyChain :: Bool
    -- ^ Obey the pre-agreement block-selection rule to use an old enough block.
    , selectionObeyAge :: Bool
    -- ^ Vote in the current round.
    , voteCurrent :: Bool
    -- ^ Obey the VR-1A voting rule.
    , voteObeyVR1A :: Bool
    -- ^ Obey the VR-1B voting rule.
    , voteObeyVR1B :: Bool
    -- ^ Obey the VR-2A voting rule.
    , voteObeyVR2A :: Bool
    -- ^ Obey the VR-2B voting rule.
    , voteObeyVR2B :: Bool
    -- ^ A certificate is included in a block only if there is no round-2 certificate.
    , certObeyRound :: Bool
    -- ^ A certificate is included in a block only if it has not expired.
    , certObeyAge :: Bool
    -- ^ A certificate is included in a block only if `cert*` is younger.
    , certObeyStar :: Bool
    -- ^ A certificate is included in a block only if it is `cert'`.
    , certObeyPrime :: Bool
    -- ^ Forbid equivocated votes.
    , noEquivocateVotes :: Bool
    }
  deriving (Eq, Generic, Ord, Read, Show)

-- | Enforce all Peras protocol rules when generating arbitrary instances.
strictGenConstraints :: GenConstraints
strictGenConstraints = MkGenConstraints False False False False False False False False False False False False False False False False False

-- | Do not enforce Peras protocol rules when generating arbitrary instances.
votingGenConstraints :: GenConstraints
votingGenConstraints = MkGenConstraints False True True True True True True True False False False False True True True True True

-- | Do not enforce Peras protocol rules when generating arbitrary instances.
lenientGenConstraints :: GenConstraints
lenientGenConstraints = MkGenConstraints False False False False False False False False False False False False False False False False False

-- | Generator size scaling for sequence of actions.
actionsSizeScaling :: Int
actionsSizeScaling = 3

genProtocol :: GenConstraints -> Gen PerasParams
genProtocol MkGenConstraints{twoParties} =
  do
    perasB <- chooseInteger (0, 20)
    perasΔ <- chooseInteger (0, 5)
    perasU <- chooseInteger (15 + 3 * perasΔ, 40)
    perasL <- chooseInteger (10, perasU - perasΔ)
    perasR <- chooseInteger (1, 4)
    let perasA = perasR * perasU
    perasK <- (perasR +) <$> chooseInteger (0, 1)
    let perasT = 0 -- Should not be used in the absence of pre-agreement.
    perasτ <-
      if twoParties
        then pure 2
        else frequency [(6, pure 2), (3, pure 3), (1, pure 4)]
    pure MkPerasParams{..}

genSelection :: GenConstraints -> NodeModel -> Chain -> Gen (Hash Block, SlotNumber)
genSelection MkGenConstraints{selectionObeyChain, selectionObeyAge} NodeModel{clock, protocol, allChains} prefChain =
  do
    chain <- if selectionObeyChain then pure prefChain else elements allChains
    if selectionObeyAge
      then pure $ case dropWhile ((> (fromIntegral clock - perasL protocol)) . fromIntegral . slotNumber) chain of
        block : _ -> (hash block, slotNumber block)
        [] -> (genesisHash, 0)
      else elements $ (genesisHash, 0) : fmap (hash &&& slotNumber) chain

genVote :: GenConstraints -> NodeModel -> Gen (Maybe Vote)
genVote gc node = genVote' gc node =<< genPartyId gc node

genVote' :: GenConstraints -> NodeModel -> PartyId -> Gen (Maybe Vote)
genVote' gc@MkGenConstraints{voteCurrent, voteObeyVR1A, voteObeyVR1B, voteObeyVR2A, voteObeyVR2B} node@NodeModel{clock, protocol} party =
  do
    prefChain <- genPrefChain gc node
    (block, blockSlot) <- genSelection gc node prefChain
    certPrime <- elements $ getCertPrimes node
    let
      party' = mkParty party mempty mempty
      certPrimeSlot = fromIntegral $ fromIntegral (round certPrime) * perasU protocol
      certStar = getCertStarRound prefChain
      r = inRound clock protocol
      vr1a = not voteObeyVR1A || round certPrime == r - 1
      vr1b = not voteObeyVR1B || blockSlot == 0 || blockSlot <= certPrimeSlot && block `elem` (hash <$> prefChain)
      vr2a = not voteObeyVR2A || fromIntegral r >= fromIntegral (round certPrime) + perasR protocol
      vr2b = not voteObeyVR2B || r > certStar && fromIntegral (r - certStar) `mod` perasK protocol == 0
    vr <- if voteCurrent then pure r else genRoundNumber gc node
    let pm = fromRight undefined . runIdentity $ createMembershipProof vr (Set.singleton party')
    if vr1a && vr1b || vr2a && vr2b
      then pure . Just . fromRight undefined . runIdentity $ createSignedVote party' vr block pm 1
      else pure Nothing

genVotes :: GenConstraints -> NodeModel -> Gen [Vote]
genVotes gc node@NodeModel{protocol = MkPerasParams{perasτ}} =
  do
    totalVoters <-
      frequency
        [ (90, choose (perasτ, 4 * perasτ `div` 3))
        , (10, choose (0, perasτ - 1))
        ]
    genVotes' gc node [otherId .. totalVoters + otherId - 1]

genVotes' :: GenConstraints -> NodeModel -> [PartyId] -> Gen [Vote]
genVotes' gc@MkGenConstraints{voteCurrent, voteObeyVR1A, voteObeyVR1B, voteObeyVR2A, voteObeyVR2B} node@NodeModel{clock, protocol} parties =
  do
    prefChain <- genPrefChain gc node
    (block, blockSlot) <- genSelection gc node prefChain
    certPrime <- elements $ getCertPrimes node
    let
      certPrimeSlot = fromIntegral $ fromIntegral (round certPrime) * perasU protocol
      certStar = getCertStarRound prefChain
      r = inRound clock protocol
      vr1a = not voteObeyVR1A || round certPrime == r - 1
      vr1b = not voteObeyVR1B || blockSlot == 0 || blockSlot <= certPrimeSlot && block `elem` (hash <$> prefChain)
      vr2a = not voteObeyVR2A || fromIntegral r >= fromIntegral (round certPrime) + perasR protocol
      vr2b = not voteObeyVR2B || r > certStar && fromIntegral (r - certStar) `mod` perasK protocol == 0
    vr <- if voteCurrent then pure r else genRoundNumber gc node
    let genOne party =
          let party' = mkParty party mempty mempty
              pm = fromRight undefined . runIdentity $ createMembershipProof vr (Set.singleton party')
           in fromRight undefined . runIdentity $ createSignedVote party' vr block pm 1
    pure $
      if vr1a && vr1b || vr2a && vr2b
        then genOne <$> parties
        else mempty

genMutatedBlock :: GenConstraints -> Block -> Gen Block
genMutatedBlock _ MkBlock{slotNumber, creatorId, parentBlock, bodyHash, certificate, leadershipProof} =
  do
    bodyHash' <- arbitrary `suchThat` (/= bodyHash)
    pure . fromRight undefined . runIdentity $
      createSignedBlock (mkParty creatorId mempty mempty) slotNumber parentBlock certificate leadershipProof bodyHash'

genNewChain :: GenConstraints -> NodeModel -> Gen Chain
genNewChain gc@MkGenConstraints{blockCurrent} node@NodeModel{clock} =
  do
    prefChain <- genPrefChain gc node
    fmap (: prefChain) $
      MkBlock
        <$> (if blockCurrent then pure clock else genSlotNumber gc node)
        <*> genPartyId gc node
        <*> pure (hashTip prefChain)
        <*> pure Nothing -- FIXME (cert1 <|> cert2)
        <*> arbitrary
        <*> arbitrary
        <*> arbitrary

genPrefChain :: GenConstraints -> NodeModel -> Gen Chain
genPrefChain MkGenConstraints{blockWeightiest} NodeModel{protocol, allChains} =
  let
    weigh :: Integer -> Block -> Integer
    weigh w MkBlock{certificate} = w + 1 + maybe 0 (const $ perasB protocol) certificate
    weights :: [(Integer, Chain)]
    weights = [(foldl weigh 0 chain, chain) | chain <- allChains]
    maxWeight = maximum $ fst <$> weights
    prefChains = snd <$> filter ((== maxWeight) . fst) weights
   in
    if blockWeightiest
      then
        if null prefChains
          then pure mempty
          else elements prefChains
      else sublistOf =<< elements allChains

getCertPrimes :: NodeModel -> [Certificate]
getCertPrimes NodeModel{allSeenCerts} =
  let certRound = maximum $ round <$> allSeenCerts
   in filter ((== certRound) . round) allSeenCerts

getCertStarRound :: Chain -> RoundNumber
getCertStarRound prefChain =
  case certificate <$> dropWhile (isNothing . certificate) prefChain of
    Just cert : _ -> round cert
    _ -> 0

genCertForBlock :: GenConstraints -> NodeModel -> Chain -> Gen (Maybe Certificate)
genCertForBlock MkGenConstraints{certObeyRound, certObeyAge, certObeyStar, certObeyPrime} node@NodeModel{clock, protocol, allSeenCerts} prefChain =
  let
    r = inRound clock protocol
    certPrimes = getCertPrimes node
    certStar = getCertStarRound prefChain
    isCertPrime :: Certificate -> Bool
    isCertPrime cert
      | certObeyPrime = cert `elem` certPrimes
      | otherwise = True
    noPenultimate :: Bool
    noPenultimate = not $ certObeyRound && any ((== r - 2) . round) allSeenCerts
    unexpired :: Certificate -> Bool
    unexpired MkCertificate{round}
      | certObeyAge = fromIntegral (r - round) <= perasA protocol
      | otherwise = True
    newer :: Certificate -> Bool
    newer cert
      | certObeyStar = round cert > certStar
      | otherwise = True
    candidates =
      filter
        (\cert -> noPenultimate && unexpired cert && isCertPrime cert && newer cert)
        allSeenCerts
   in
    elements $ Nothing : fmap Just candidates

genCert :: GenConstraints -> NodeModel -> Chain -> Gen (Maybe Certificate)
genCert MkGenConstraints{} NodeModel{clock, protocol} prefChain =
  let
    r = inRound clock protocol
    validCertRounds = [1 .. r] -- \\ (round <$> Map.keys certs)
   in
    if null prefChain || null validCertRounds
      then pure Nothing
      else fmap Just . MkCertificate <$> elements validCertRounds <*> (hash <$> elements prefChain)

genSlotNumber :: GenConstraints -> NodeModel -> Gen SlotNumber
genSlotNumber _ NodeModel{clock} =
  MkSlotNumber <$> chooseInteger (0, getSlotNumber clock)

genRoundNumber :: GenConstraints -> NodeModel -> Gen RoundNumber
genRoundNumber _ NodeModel{clock, protocol} =
  MkRoundNumber <$> chooseInteger (1, getRoundNumber $ inRound clock protocol)

genPartyId :: GenConstraints -> NodeModel -> Gen PartyId
genPartyId MkGenConstraints{twoParties} NodeModel{protocol = MkPerasParams{perasτ}} =
  if twoParties
    then pure otherId
    else choose (sutId, sutId + 4 * perasτ `div` 3)

genSlotLeadership :: Double -> SlotNumber -> Gen [SlotNumber]
genSlotLeadership fraction limit =
  filterM (const $ chooseFraction fraction) [1 .. limit]

genCommitteeMembership :: Double -> RoundNumber -> Gen [RoundNumber]
genCommitteeMembership fraction limit =
  filterM (const $ chooseFraction fraction) [1 .. limit]

chooseFraction :: Double -> Gen Bool
chooseFraction fraction = (<= fraction) <$> choose (0, 1)

genHonestTick :: Bool -> GenConstraints -> NodeModel -> Gen (([Chain], [Vote]), NodeModel)
genHonestTick obeyDelta MkGenConstraints{} node@NodeModel{clock, protocol = params@MkPerasParams{perasΔ}, allChains, allVotes} =
  do
    delta <- fromIntegral <$> if obeyDelta then choose (1, perasΔ) else getNonNegative <$> arbitrary
    let votingSlot = slotInRound params clock == 0
    sortition' <-
      elements $
        [(const True, const False)]
          ++ [(const False, const True) | votingSlot]
          ++ [(const True, const True) | votingSlot]
    let ((newChains, newVotes), node') = second (\n -> n{clock = clock - 1}) $ rollbackNodeModel delta node
    newChains' <- sublistOf newChains
    newVotes' <- sublistOf newVotes
    let
      addChain s = maybe s snd . transition sortition' s . NewChain
      addVote s = maybe s snd . transition sortition' s . NewVote
      reassignTip [] = []
      reassignTip (b : bs) = b{Peras.Block.creatorId = otherId} : bs
      reassignVote v = v{Peras.Chain.creatorId = otherId}
      doTick s =
        maybe
          ((mempty, mempty), s)
          (first $ filter (`notElem` allChains) . fmap reassignTip *** filter (`notElem` allVotes) . fmap reassignVote)
          $ transition sortition' s Tick
    pure $
      doTick $
        flip (foldl addVote) newVotes' $
          foldl addChain node' newChains'

rollbackNodeModel :: Int -> NodeModel -> (([Chain], [Vote]), NodeModel)
rollbackNodeModel delta s@NodeModel{..} =
  let
    clock' = max 1 $ clock - fromIntegral delta
    round' = inRound clock' protocol
    keepBlock MkBlock{slotNumber} = slotNumber <= clock'
    keepChain = all keepBlock
    -- This is approximate because we don't known when the vote was received.
    keepVote MkVote{votingRound} = votingRound <= round'
    -- This is approximate because we don't known when the certificate was received.
    keepCert cert@MkCertificate{round} = cert == genesisCert || round <= round' && cert `elem` nub (mapMaybe certificate `concatMap` allChains')
    (allChains', newChains) = partition keepChain allChains
    (allVotes', newVotes) = partition keepVote allVotes
   in
    ( (newChains, newVotes)
    , s
        { clock = clock'
        , allChains = allChains'
        , allVotes = allVotes'
        , allSeenCerts = filter keepCert allSeenCerts
        }
    )
