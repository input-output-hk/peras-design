{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.Protocol.Types (
  Protocol(..)
) where

import GHC.Generics (Generic)

import qualified Data.Aeson as A
import qualified Data.Aeson.Types as A

data Protocol =
    PseudoPraos  -- | Low-fidelity version of OuroborosPraos.
    {
      activeSlotCoefficient :: Double
    }
  | PseudoPeras  -- | Low-fidelity version of Ouroboros Peras.
    {
      activeSlotCoefficient :: Double
    , roundDuration :: Int
    , meanCommitteeSize :: Int
    , votingBoost :: Double
    , votingWindow :: (Int, Int)
    , votingQuorum :: Int
    }
  | OuroborosPraos  -- | High-fidelity version of Ouroboros Praos.
  | OuroborosGenesis  -- | High-fidelity version of Ouroboros Genesis.
  | OuroborosPeras  -- | High-fidelity version of Ouroboros Peras.
    deriving stock (Eq, Generic, Ord, Read, Show)

instance A.FromJSON Protocol where
  parseJSON =
    A.withObject "Protocol"
      $ \o ->
        do
          protocol <- o A..: "protocol"
          case protocol of
            "PseudoPraos" ->
              PseudoPraos
                <$> o A..: "activeSlotCoefficient"
            "PseudoPeras" ->
              PseudoPeras
                <$> o A..: "activeSlotCoefficient"
                <*> o A..: "meanCommitteeSize"
                <*> o A..: "roundDuration"
                <*> o A..: "votingBoost"
                <*> o A..: "votingWindow"
                <*> o A..: "votingQuorum"
            "OuroborosPraos" ->
              pure OuroborosPraos
            "OuroborosGenesis" ->
              pure OuroborosGenesis
            "OuroborosPeras" ->
              pure OuroborosPeras
            _ -> A.parseFail protocol

instance A.ToJSON Protocol where
  toJSON PseudoPraos{..} =
    A.object
      [
        "protocol" A..= ("PseudoPraos" :: String)
      , "activeSlotCoefficient" A..= activeSlotCoefficient
      ]
  toJSON PseudoPeras{..} =
    A.object
      [
        "protocol" A..= ("PseudoPeras" :: String)
      , "activeSlotCoefficient" A..= activeSlotCoefficient
      , "meanCommitteeSize" A..= meanCommitteeSize
      , "roundDuration" A..= roundDuration
      , "votingBoost" A..= votingBoost
      , "votingWindow" A..= votingWindow
      ]
  toJSON OuroborosPraos =
    A.object
      [
        "protocol" A..= ("OuroborosPraos" :: String)
      ]
  toJSON OuroborosGenesis =
    A.object
      [
        "protocol" A..= ("OuroborosGenesis" :: String)
      ]
  toJSON OuroborosPeras =
    A.object
      [
        "protocol" A..= ("OuroborosPeras" :: String)
      ]
