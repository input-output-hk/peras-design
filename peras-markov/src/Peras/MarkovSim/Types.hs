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

newtype Evolution = MkEvolution {getEvolution :: Map Chains Probability}
  deriving stock (Eq, Show)

instance Default Evolution where
  def = MkEvolution $ Map.singleton def 1

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
  }
  deriving stock (Eq, Generic, Ord, Show)

instance Default Chains where
  def = MkChains 0 0 def def

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
