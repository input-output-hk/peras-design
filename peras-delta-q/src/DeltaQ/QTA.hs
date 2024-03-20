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
fromQTA steps = go (fromDouble 0.0) steps
 where
  stepf (p, v) acc =
    let delta = (v - acc)
     in (K p delta, delta)

  go acc = \case
    (q :| (x : rest)) ->
      let (step, delta) = stepf q acc
       in step `Plus` ShiftRight delta (go (acc + delta) (x :| rest))
    (q :| []) ->
      fst $ stepf q acc
