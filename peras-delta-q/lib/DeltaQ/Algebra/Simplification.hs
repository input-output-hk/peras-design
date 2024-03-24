module DeltaQ.Algebra.Simplification
where

import DeltaQ.Algebra.Type


{- Normal form
  * promotes ⊥ to up and to the left
  * demotes ∅ down and to the right
  in any expression.
-}

normaliseDeltaQ:: (Ord p,Fractional p, DelayModel d n)
                  => DeltaQ p d n -> DeltaQ p d n

-- eliminate redundant choices when both terms are ⊥ or ∅
normaliseDeltaQ (ProbChoice _ Bottom Bottom)
  = Bottom
normaliseDeltaQ (ProbChoice _ Unit Unit)
  = Unit

-- eliminate redundant branching if probability is 0 or 1.  use of <=
-- and >= is to permit (however unwisely) Real versions of probability
normaliseDeltaQ (ProbChoice prob a b)
  | prob <= 0  = normaliseDeltaQ b -- a has no influence
  | prob >= 1  = normaliseDeltaQ a -- b has no influence

-- normalise the position of ⊥ and ∅
normaliseDeltaQ (ProbChoice p a Bottom)
  = let a' = normaliseDeltaQ a
    in normaliseDeltaQ $ ProbChoice (1-p) Bottom a'
normaliseDeltaQ (ProbChoice p Unit b)
  = let b' = normaliseDeltaQ b
    in normaliseDeltaQ $ ProbChoice (1-p) b' Unit

-- structural re-writes for ProbChoice
-- ⊥ concatenation
normaliseDeltaQ (ProbChoice p Bottom (ProbChoice q Bottom x))
  = let x' = normaliseDeltaQ x
    in normaliseDeltaQ $ ProbChoice ( p + (1-p) * q) Bottom x'
--
-- visualisation of ⊥ concatenation:
--       A                                                 A
--   (p)/ \(1-p)     noting that               (p+(1-p)*q)/ \((1-p)*(1-q))
--     ⊥   B                       becomes               ⊥  x
--     (q)/ \(1-q)   the ⊥ branch
--       ⊥   x       B probability             and that 1 - (p+(1-p*q) = (1-p)*(1-q)
--                   is (1-p)*q

-- ∅ demotion
normaliseDeltaQ (ProbChoice q (ProbChoice p x Unit) y)
    = let x' = normaliseDeltaQ x
          y' = normaliseDeltaQ y
      in normaliseDeltaQ $ ProbChoice (p*q) x' (ProbChoice ((1 - q)/(1 - p*q)) y' Unit)

-- operational identities for ⊕
normaliseDeltaQ (Convolve Bottom _)
  = Bottom
normaliseDeltaQ (Convolve _ Bottom)
  = Bottom
normaliseDeltaQ (Convolve Unit y)
  = normaliseDeltaQ y
normaliseDeltaQ (Convolve x Unit)
  = normaliseDeltaQ x

-- ⊥ promotion
normaliseDeltaQ (Convolve (ProbChoice p Bottom x) y)
  = normaliseDeltaQ $ ProbChoice p Bottom (Convolve x y)
normaliseDeltaQ (Convolve x (ProbChoice p Bottom y))
  = normaliseDeltaQ $ ProbChoice p Bottom (Convolve x y)

-- ∅ elimination
normaliseDeltaQ (Convolve (ProbChoice p x Unit) y)
  = normaliseDeltaQ $ ProbChoice p (Convolve x y) y
normaliseDeltaQ (Convolve x (ProbChoice p y Unit))
  = normaliseDeltaQ $ ProbChoice p (Convolve x y) x

-- delay model simplification
normaliseDeltaQ x@(Convolve (Delay _) (Delay _))
 = simplifyDelay normaliseDeltaQ x

normaliseDeltaQ x = x
