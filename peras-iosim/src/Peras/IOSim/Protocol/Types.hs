{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.Protocol.Types (
  Protocol(..)
) where

import GHC.Generics (Generic)

import qualified Data.Aeson as A

data Protocol =
    PraosProtocol
    {
      activeSlotCoefficient :: Double
    }
  | GenesisProtocol
  | PerasProtocol
    {
      activeSlotCoefficient :: Double
    , roundDuration :: Int
    , votingBoost :: Double
    , votingWindow :: (Int, Int)
    , votingQuorum :: Int
    }
    deriving stock (Eq, Generic, Ord, Read, Show)

instance A.FromJSON Protocol where
  parseJSON =
    A.withObject "Protocol"
      $ \o ->
        do
          protocol <- o A..: "protocol"
          case protocol of
            "Praos" ->
              PraosProtocol
                <$> o A..: "activeSlotCoefficient"
            "Genesis" ->
              pure GenesisProtocol
            "Peras" ->
              PerasProtocol
                <$> o A..: "activeSlotCoefficient"
                <*> o A..: "roundDuration"
                <*> o A..: "votingBoost"
                <*> o A..: "votingWindow"
                <*> o A..: "votingQuorum"
            _ -> fail protocol

instance A.ToJSON Protocol where
  toJSON PraosProtocol{..} =
    A.object
      [
        "protocol" A..= ("Praos" :: String)
      , "activeSlotCoefficient" A..= activeSlotCoefficient
      ]
  toJSON GenesisProtocol =
    A.object
      [
        "protocol" A..= ("Genesis" :: String)
      ]
  toJSON PerasProtocol{..} =
    A.object
      [
        "protocol" A..= ("Peras" :: String)
      , "activeSlotCoefficient" A..= activeSlotCoefficient
      , "roundDuration" A..= roundDuration
      , "votingBoost" A..= votingBoost
      , "votingWindow" A..= votingWindow
      ]
