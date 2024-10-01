{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -fno-warn-missing-pattern-synonym-signatures #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module Peras.Conformance.Params where

import Data.Aeson (FromJSON, ToJSON)
import qualified Data.Aeson as A
import Data.Default (Default (..))
import GHC.Generics (Generic)

data PerasParams = MkPerasParams
  { perasU :: Integer
  , perasA :: Integer
  , perasR :: Integer
  , perasK :: Integer
  , perasL :: Integer
  , perasτ :: Integer
  , perasB :: Integer
  , perasT :: Integer
  , perasΔ :: Integer
  }
  deriving (Eq, Generic, Show)

defaultPerasParams :: PerasParams
defaultPerasParams = MkPerasParams 20 200 10 17 10 3 10 15 5

instance FromJSON PerasParams where
  parseJSON =
    A.withObject "PerasParams" $ \o -> do
      perasU <- o A..: "U"
      perasA <- o A..: "A"
      perasR <- o A..: "R"
      perasK <- o A..: "K"
      perasL <- o A..: "L"
      perasτ <- o A..: "τ"
      perasB <- o A..: "B"
      perasT <- o A..: "T"
      perasΔ <- o A..: "Δ"
      pure MkPerasParams{..}

instance ToJSON PerasParams where
  toJSON MkPerasParams{..} =
    A.object
      [ "U" A..= perasU
      , "A" A..= perasA
      , "R" A..= perasR
      , "K" A..= perasK
      , "L" A..= perasL
      , "τ" A..= perasτ
      , "B" A..= perasB
      , "T" A..= perasT
      , "Δ" A..= perasΔ
      ]

-- FIXME: What are the actual values of T_heal, T_CQ, and T_CP?
-- For now I am assuming they all are in the order of security parameter, eg. 2160 on mainnet.
instance Default PerasParams where
  def = defaultPerasParams
