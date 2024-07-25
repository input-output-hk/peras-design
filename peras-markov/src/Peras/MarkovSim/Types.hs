{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StrictData #-}

module Peras.MarkovSim.Types where

import Data.Aeson (FromJSON, ToJSON)
import Data.Default (Default (def))
import Data.Function (on)
import Data.List (sort)
import Data.Map.Strict (Map)
import GHC.Generics (Generic)
import Peras.Foreign (IsCommitteeMember, IsSlotLeader)
import Prettyprinter (Pretty (pretty), fill, vsep, (<+>))
import Statistics.Distribution (complCumulative, cumulative)
import Statistics.Distribution.Binomial (binomial)

import qualified Data.Map.Strict as Map

type Slot = Int

type Round = Int

type Stake = Int

type Votes = Int

type Probability = Double

data Peras = MkPeras
  { α :: Double
  , u :: Slot
  , a :: Slot
  , r :: Round
  , k :: Round
  , b :: Int
  , τ :: Votes
  , c :: Votes
  }
  deriving stock (Eq, Generic, Show)

instance Default Peras where
  def = MkPeras 0.05 150 500 10 20 10 75 100

instance FromJSON Peras
instance ToJSON Peras

newRound :: Peras -> Slot -> Bool
newRound MkPeras{u} s = s `mod` u == 0

inRound :: Peras -> Slot -> Round
inRound MkPeras{u} s = s `div` u

data Probabilities = MkProbabilities
  { noBlock :: Probability
  , honestBlock :: Probability
  , adversaryBlock :: Probability
  , mixedBlocks :: Probability
  , noQuorum :: Probability
  , honestQuorum :: Probability
  , adversaryQuorum :: Probability
  , mixedQuorum :: Probability
  }
  deriving stock (Eq, Generic, Show)

instance Default Probabilities where
  def = mkProbabilities def 1000 0

mkProbabilities :: Peras -> Stake -> Stake -> Probabilities
mkProbabilities MkPeras{α, τ, c} honestStake adversaryStake =
  let
    (//) = on (/) fromIntegral
    τ' = fromIntegral τ - 1

    totalStake = honestStake + adversaryStake

    p = honestStake // totalStake
    q = adversaryStake // totalStake

    p' = 1 - (1 - α) ** p
    q' = 1 - (1 - α) ** q

    noBlock = (1 - p') * (1 - q')
    honestBlock = p' * (1 - q')
    adversaryBlock = (1 - p') * q'
    mixedBlocks = p' * q'

    beta = c // totalStake

    noQuorum = binomial totalStake beta `cumulative` τ'
    honestQuorum = binomial honestStake beta `complCumulative` τ'
    adversaryQuorum = binomial adversaryStake beta `complCumulative` τ'
    mixedQuorum = 1 - noQuorum - honestQuorum - adversaryQuorum
   in
    MkProbabilities{..}

pureProbabilities :: IsSlotLeader -> IsCommitteeMember -> Probabilities
pureProbabilities isLeader isMember =
  MkProbabilities
    { noBlock = if isLeader then 0 else 1
    , honestBlock = if isLeader then 1 else 0
    , adversaryBlock = 0
    , mixedBlocks = 0
    , noQuorum = if isMember then 0 else 1
    , honestQuorum = if isMember then 1 else 0
    , adversaryQuorum = 0
    , mixedQuorum = 0
    }

newtype Evolution = MkEvolution {getEvolution :: Map Chains Probability}
  deriving stock (Eq, Show)

instance Default Evolution where
  def = behavioralEvolution def

behavioralEvolution :: Behavior -> Evolution
behavioralEvolution b = MkEvolution $ Map.singleton def{behavior = b} 1

instance Pretty Evolution where
  pretty MkEvolution{getEvolution} =
    let prettyChain MkChain{..} =
          fill 6 (pretty weight)
            <+> fill 6 (pretty certStar)
            <+> fill 6 (maybe (pretty "") pretty certStarNext)
            <+> fill 6 (pretty certPrime)
            <+> fill 6 (maybe (pretty "") pretty certPrimeNext)
            <+> fill
              5
              ( pretty (if certUltimate then "⊤" else "⊥")
                  <> pretty (if certPenultimate then "⊤" else "⊥")
                  <> pretty (if certAntepenultimate then "⊤" else "⊥")
              )
        pretty' (MkChains{..}, probability) =
          fill 6 (pretty slot)
            <+> fill 6 (pretty prefix)
            <+> prettyChain honest
            <+> prettyChain adversary
            <+> pretty probability
        header =
          [ pretty "              honest                                   adversarial"
          , pretty "              ---------------------------------------- ----------------------------------------"
          , pretty "slot   prefix weight cert*  [next] cert'  [next] certs weight cert*  [next] cert'  [next] certs probability"
          , pretty "------ ------ ------ ------ ------ ------ ------ ----- ------ ------ ------ ------ ------ ----- ------------------------"
          ]
        footer =
          [ pretty ""
          , pretty "Deficit:" <+> pretty (1 - sum getEvolution)
          ]
        rows = pretty' <$> sort (Map.toList getEvolution)
     in vsep $ header <> rows <> footer

data Chains = MkChains
  { slot :: Slot
  , prefix :: Slot
  , honest :: Chain
  , adversary :: Chain
  , publicWeight :: Int
  , behavior :: Behavior
  }
  deriving stock (Eq, Generic, Ord, Show)

instance Default Chains where
  def = MkChains 0 0 def def minBound def

data Chain = MkChain
  { weight :: Int
  , certPrime :: Round
  , certPrimeNext :: Maybe Round
  , certUltimate :: Bool
  , certPenultimate :: Bool
  , certAntepenultimate :: Bool
  , certStar :: Round
  , certStarNext :: Maybe Round
  }
  deriving stock (Eq, Generic, Ord, Show)

instance Default Chain where
  def = MkChain 1 0 Nothing True False False 0 Nothing

data Behavior = MkBehavior
  { adverseVoting :: AdverseVoting
  , adverseRevelation :: AdverseRevelation
  , adverseAdoption :: AdverseAdoption
  , adverseBlocks :: AdverseBlocks
  , adverseCertification :: AdverseCertification
  , addverseSplitting :: AdverseSplitting
  }
  deriving (Eq, Generic, Ord, Show)

instance FromJSON Behavior
instance ToJSON Behavior

-- The default adversarial behavior is full honesty.
instance Default Behavior where
  def = honestChainBehavior

-- | An honest adversary.
honestChainBehavior :: Behavior
honestChainBehavior = MkBehavior AlwaysVote AlwaysReveal AdoptIfLonger PromptBlocks PromptVotes NoSplitting

-- | Build and vote for a private chain.
privateChainBehavior :: Behavior
privateChainBehavior = MkBehavior VoteForAdversary NeverReveal NeverAdopt PromptBlocks PromptVotes NoSplitting

-- | A temporarily split network.
splitChainBehavior :: (Slot, Slot) -> Behavior
splitChainBehavior (splitStart, splitFinish) = MkBehavior AlwaysVote AlwaysReveal AdoptIfLonger PromptBlocks PromptVotes MkAdverseSplit{..}

data AdverseVoting = NeverVote | AlwaysVote | VoteForAdversary
  deriving (Eq, Generic, Ord, Show)

instance FromJSON AdverseVoting
instance ToJSON AdverseVoting

data AdverseRevelation = NeverReveal | AlwaysReveal | RevealIfLonger
  deriving (Eq, Generic, Ord, Show)

instance FromJSON AdverseRevelation
instance ToJSON AdverseRevelation

data AdverseAdoption = NeverAdopt | AdoptIfLonger
  deriving (Eq, Generic, Ord, Show)

instance FromJSON AdverseAdoption
instance ToJSON AdverseAdoption

data AdverseBlocks = PromptBlocks
  -- TODO: Add `| DelayBlocks Int` to indicate that blocks are diffused late by a specified number of slots.
  deriving (Eq, Generic, Ord, Show)

instance FromJSON AdverseBlocks
instance ToJSON AdverseBlocks

data AdverseCertification = PromptVotes
  -- TODO: Add `| DelayVotes` to indicate that votes are diffused as late as possible.
  deriving (Eq, Generic, Ord, Show)

instance FromJSON AdverseCertification
instance ToJSON AdverseCertification

data AdverseSplitting
  = NoSplitting
  | MkAdverseSplit
      { splitStart :: Slot
      , splitFinish :: Slot
      }
  deriving (Eq, Generic, Ord, Show)

instance FromJSON AdverseSplitting
instance ToJSON AdverseSplitting
