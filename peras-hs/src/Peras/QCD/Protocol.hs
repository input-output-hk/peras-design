{-# LANGUAGE DeriveGeneric #-}

module Peras.QCD.Protocol where

import Numeric.Natural (Natural)

import Data.Default (Default (..))
import GHC.Generics (Generic)

data ParamSymbol
  = U
  | A
  | W
  | L
  | B
  | Τ
  | R
  | K

τ :: ParamSymbol
τ = Τ

data Params = Params
  { paramU :: Natural
  , paramA :: Natural
  , paramW :: Natural
  , paramL :: Natural
  , paramB :: Natural
  , paramΤ :: Natural
  , paramR :: Natural
  , paramK :: Natural
  }
  deriving (Eq, Generic, Show)

defaultParams :: Params
defaultParams = Params 120 240 3600 120 10 300 120 600

instance Default Params where
  def = defaultParams

perasParam :: ParamSymbol -> Params -> Natural
perasParam U = \r -> paramU r
perasParam A = \r -> paramA r
perasParam W = \r -> paramW r
perasParam L = \r -> paramL r
perasParam B = \r -> paramB r
perasParam Τ = \r -> paramΤ r
perasParam R = \r -> paramR r
perasParam K = \r -> paramK r
