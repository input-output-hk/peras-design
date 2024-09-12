{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.Conformance.Generators where

import Control.Applicative
import Control.Arrow
import Data.Maybe
import Debug.Trace
import Debug.Trace (traceShow)
import GHC.Generics (Generic)
import Peras.Arbitraries ()
import Peras.Block
import Peras.Chain
import Peras.Conformance.Model
import Peras.Crypto
import Peras.Numbering
import Peras.Prototype.Types (PerasParams (..), hashTip, inRound)
import Test.QuickCheck
import Prelude hiding (round)

-- | Constraints on generating Peras values.
data GenConstraints
  = -- | Whether to use consistent and semi-realistic protocol parameters.
    MkGenConstraints
    { useTestParams :: Bool
    -- ^ Don't generate protocol parameters.
    , realisticProtocol :: Bool
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
strictGenConstraints = MkGenConstraints False False False False False False False False False False False False False False False False False False

-- | Do not enforce Peras protocol rules when generating arbitrary instances.
votingGenConstraints :: GenConstraints
votingGenConstraints = MkGenConstraints False True True True True True True True True False False False False True True True True True

-- | Do not enforce Peras protocol rules when generating arbitrary instances.
lenientGenConstraints :: GenConstraints
lenientGenConstraints = MkGenConstraints False False False False False False False False False False False False False False False False False False

genProtocol :: GenConstraints -> Gen PerasParams
genProtocol MkGenConstraints{realisticProtocol, twoParties}
  | realisticProtocol =
      do
        perasB <- chooseInteger (0, 20)
        perasΔ <- chooseInteger (0, 5)
        perasU <- chooseInteger (60 + 3 * perasΔ, 120)
        perasL <- chooseInteger (20 + perasΔ, perasU)
        perasR <- chooseInteger (1, 10)
        let perasA = perasR * perasU
        perasK <- (perasR +) <$> chooseInteger (0, 2)
        let perasT = 0 -- Should not be used in the absence of pre-agreement.
        perasτ <- frequency [(10, pure 1), (if twoParties then 0 else 1, chooseInteger (0, 3))]
        pure MkPerasParams{..}
  | otherwise =
      do
        perasB <- chooseInteger (0, 100)
        perasΔ <- chooseInteger (0, 10)
        perasU <- chooseInteger (10 + perasΔ, 500)
        perasL <- chooseInteger (1 + perasΔ, perasU)
        perasR <- chooseInteger (1, 100)
        perasA <- ((perasR * perasU) +) <$> chooseInteger (-10, 30)
        perasK <- (perasR +) <$> chooseInteger (0, 10)
        let perasT = 0 -- Should not be used in the absence of pre-agreement.
        perasτ <- frequency [(10, pure 1), (if twoParties then 0 else 1, chooseInteger (0, 3))]
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
genVote gc@MkGenConstraints{voteCurrent, voteObeyVR1A, voteObeyVR1B, voteObeyVR2A, voteObeyVR2B} node@NodeModel{clock, protocol} =
  do
    prefChain <- genPrefChain gc node
    (block, blockSlot) <- genSelection gc node prefChain
    certPrime <- elements $ getCertPrimes node
    party <- genPartyId gc node
    let
      certPrimeSlot = fromIntegral $ fromIntegral (round certPrime) * perasU protocol
      certStar = getCertStarRound prefChain
      r = inRound clock protocol
      vr1a = not voteObeyVR1A || round certPrime == r - 1
      vr1b = not voteObeyVR1B || blockSlot == 0 || blockSlot <= certPrimeSlot && block `elem` (hash <$> prefChain)
      vr2a = not voteObeyVR2A || fromIntegral r >= fromIntegral (round certPrime) + perasR protocol
      vr2b = not voteObeyVR2B || r > certStar && fromIntegral (r - certStar) `mod` perasK protocol == 0
    if vr1a && vr1b || vr2a && vr2b
      then
        fmap Just $
          MkVote
            <$> (if voteCurrent then pure r else genRoundNumber gc node)
            <*> pure party
            <*> arbitrary
            <*> pure block
            <*> arbitrary
      else pure Nothing

genNewChain :: GenConstraints -> NodeModel -> Gen Chain
genNewChain gc@MkGenConstraints{blockCurrent} node@NodeModel{clock} =
  do
    prefChain <- genPrefChain gc node
    cert1 <- genCertForBlock gc node prefChain
    cert2 <- genCert gc node prefChain -- FIXME: Guard this with a setting.
    fmap (: prefChain) $
      MkBlock
        <$> (if blockCurrent then pure clock else genSlotNumber gc node)
        <*> genPartyId gc node
        <*> pure (hashTip prefChain)
        <*> pure Nothing -- FIXME (cert1 <|> cert2)
        <*> arbitrary
        <*> arbitrary
        <*> arbitrary

genPrefChain gc@MkGenConstraints{blockWeightiest} node@NodeModel{protocol, allChains} =
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
getCertPrimes NodeModel{clock, protocol, allSeenCerts} =
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
  MkRoundNumber <$> chooseInteger (0, getRoundNumber $ inRound clock protocol)

genPartyId :: GenConstraints -> NodeModel -> Gen PartyId
genPartyId MkGenConstraints{twoParties} _ =
  if twoParties
    then pure otherId
    else (max sutId otherId +) . getPositive <$> arbitrary
