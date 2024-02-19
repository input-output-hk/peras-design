{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.Protocol.Types (
  Protocol (..),
) where

import GHC.Generics (Generic)

import qualified Data.Aeson as A
import qualified Data.Aeson.Types as A

data Protocol
  = PseudoPraos
      { activeSlotCoefficient :: Double
      -- ^ Low-fidelity version of OuroborosPraos.
      }
  | PseudoPeras
      { activeSlotCoefficient :: Double
      -- ^ Low-fidelity version of Ouroboros Peras.
      , roundDuration :: Int
      , pCommitteeLottery :: Double
      , votingBoost :: Double
      , votingWindow :: (Int, Int)
      , votingQuorum :: Int
      , voteMaximumAge :: Int
      , cooldownDuration :: Int
      , prefixCutoffWeight :: Double
      }
  | OuroborosPraos
  | -- | High-fidelity version of Ouroboros Praos.
    OuroborosGenesis
  | -- | High-fidelity version of Ouroboros Genesis.
    OuroborosPeras
  -- \| High-fidelity version of Ouroboros Peras.
  deriving stock (Eq, Generic, Ord, Read, Show)

instance A.FromJSON Protocol where
  parseJSON =
    A.withObject "Protocol" $
      \o ->
        do
          protocol <- o A..: "protocol"
          case protocol of
            "PseudoPraos" ->
              PseudoPraos
                <$> o A..: "activeSlotCoefficient"
            "PseudoPeras" ->
              PseudoPeras
                <$> o A..: "activeSlotCoefficient"
                <*> o A..: "pCommitteeLottery"
                <*> o A..: "roundDuration"
                <*> o A..: "votingBoost"
                <*> o A..: "votingWindow"
                <*> o A..: "votingQuorum"
                <*> o A..: "voteMaximumAge"
                <*> o A..: "cooldownDuration"
                <*> o A..: "prefixCutoffWeight"
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
      [ "protocol" A..= ("PseudoPraos" :: String)
      , "activeSlotCoefficient" A..= activeSlotCoefficient
      ]
  toJSON PseudoPeras{..} =
    A.object
      [ "protocol" A..= ("PseudoPeras" :: String)
      , "activeSlotCoefficient" A..= activeSlotCoefficient
      , "pCommitteeLottery" A..= pCommitteeLottery
      , "roundDuration" A..= roundDuration
      , "votingBoost" A..= votingBoost
      , "votingWindow" A..= votingWindow
      , "voteMaximumAge" A..= voteMaximumAge
      , "cooldownDuration" A..= cooldownDuration
      , "prefixCutoffWeight" A..= prefixCutoffWeight
      ]
  toJSON OuroborosPraos =
    A.object
      [ "protocol" A..= ("OuroborosPraos" :: String)
      ]
  toJSON OuroborosGenesis =
    A.object
      [ "protocol" A..= ("OuroborosGenesis" :: String)
      ]
  toJSON OuroborosPeras =
    A.object
      [ "protocol" A..= ("OuroborosPeras" :: String)
      ]
