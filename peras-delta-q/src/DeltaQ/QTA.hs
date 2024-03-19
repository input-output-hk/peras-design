module DeltaQ.QTA where

import A (A (..))
import Data.List.NonEmpty (NonEmpty ((:|)))
import Reals (Rops (..), fromDouble)
import UnitInterval (Iops)
import Prelude hiding ((+), (-))

-- | Construct a ΔQ initial distribution from a sequence of "steps".
--
-- Given a sequence of `(probability, value)` pairs, construct an `A`
-- expression where each value is considered as a step function with
-- given uniform probability.  The values must be monotonically
-- increasing and the sum of probabilities be lower than 1.
fromQTA :: (Rops r, Iops i) => NonEmpty (i, r) -> A r i
fromQTA steps = go steps (fromDouble 0.0)
 where
  go ((p, v) :| (x : rest)) acc =
    let step = K p delta
        delta = (v - acc)
     in step `Plus` ShiftRight delta (go (x :| rest) (acc + delta))
  go ((p, v) :| []) acc =
    let step = K p delta
        delta = (v - acc)
     in step
