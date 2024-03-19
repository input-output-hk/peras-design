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

praosHeader :: (Rops r, Iops i) => A r i
praosHeader =
  fromQTA $
    fromList
      [(oneThird, toR 0.012), (oneThird, toR 0.069), (oneThird, toR 0.268)]

praosBody :: (Rops r, Iops i) => A r i
praosBody =
  fromQTA $
    fromList [(oneThird, toR 0.024), (oneThird, toR 0.143), (oneThird, toR 0.531)]

toI :: Iops i => Double -> i
toI = UnitInterval.fromDouble

toR :: Rops r => Double -> r
toR = Reals.fromDouble

oneThird :: Iops i => i
oneThird = toI $ fromRational $ 1 % 3
