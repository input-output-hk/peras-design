-- | ΔQ models for Praos and Peras.
module Peras where

import A (A (..))
import Data.List.NonEmpty (fromList)
import Data.Ratio ((%))
import DeltaQ.QTA (fromQTA)
import Reals (Rops)
import qualified Reals
import UnitInterval (Iops)
import qualified UnitInterval

singleMTURoundtrip :: (Rops r, Iops i) => A r i
singleMTURoundtrip =
  fromQTA $
    fromList [(oneThird, toR 0.012), (oneThird, toR 0.069), (oneThird, toR 0.268)]

payload64KRoundtrip :: (Rops r, Iops i) => A r i
payload64KRoundtrip =
  fromQTA $
    fromList [(oneThird, toR 0.024), (oneThird, toR 0.143), (oneThird, toR 0.531)]

headerBodyDiffusion :: (Rops r, Iops i) => A r i
headerBodyDiffusion =
  singleMTURoundtrip `Conv` singleMTURoundtrip -- `Conv` singleMTURoundtrip `Conv` payload64KRoundtrip

multihopsDiffusion :: (Rops r, Iops i) => Int -> A r i -> A r i
multihopsDiffusion n base =
  foldl Conv base $ replicate (n - 1) base

toI :: Iops i => Double -> i
toI = UnitInterval.fromDouble

toR :: Rops r => Double -> r
toR = Reals.fromDouble

oneThird :: Iops i => i
oneThird = toI $ fromRational $ 1 % 3
