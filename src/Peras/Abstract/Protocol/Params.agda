
module Peras.Abstract.Protocol.Params where

{-# FOREIGN AGDA2HS
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
#-}

{-# FOREIGN AGDA2HS
import Data.Aeson (FromJSON, ToJSON)
import qualified Data.Aeson as A
import Data.Default (Default (..))
import GHC.Generics (Generic)
#-}

open import Haskell.Prelude

record PerasParams : Set where
  constructor MkPerasParams
  field
    perasU : Integer
    -- ^ Round length, in slots
    perasA : Integer
    -- ^ Certificate expiration age, in slots
    perasR : Integer
    -- ^ Length of chain-ignorance period, in rounds
    perasK : Integer
    -- ^ Length of cool-down period, in rounds
    perasL : Integer
    -- ^ Minimum age for voted block, in slots
    perasτ : Integer
    -- ^ Quorum size, as a percentage of total expected votes
    perasB : Integer
    -- ^ Certificate boost, in blocks
    perasT : Integer
    -- ^ Termination bound for preagreement, in slots
    perasΔ : Integer
    -- ^ Delivery guarantee for diffusion, in slots

open PerasParams public
{-# COMPILE AGDA2HS PerasParams deriving (Eq, Generic, Show) #-}

defaultPerasParams : PerasParams
defaultPerasParams =
  record
    { perasU = 20
    ; perasA = 200
    ; perasR = 10
    ; perasK = 17
    ; perasL = 10
    ; perasτ = 3
    ; perasB = 10
    ; perasT = 15
    ; perasΔ = 5
    }


{-# COMPILE AGDA2HS defaultPerasParams #-}

{-# FOREIGN AGDA2HS

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
#-}
