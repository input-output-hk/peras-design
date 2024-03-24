{-# LANGUAGE FlexibleContexts #-}
module DeltaQ.Algebra
  ( module DeltaQ.Algebra.Class
  , module DeltaQ.Algebra.Simplification
  , perfection
  , bottom
  , mmmv
  , lossprob
  )
where

import DeltaQ.Algebra.Class
import DeltaQ.Algebra.Simplification

-- | No quality attenutation, zero ∆Q
perfection :: DeltaQ p d n
perfection = Unit

-- | total quality attentuation, unbounded ∆Q
bottom :: DeltaQ p d n
bottom = Bottom

-- | extract the min, max, mean and variance from DeltaQ
mmmv :: ( Fractional p, Real p, Fractional n, DelayModel d n
        , SimpleStatDesc d n) =>
        DeltaQ p d n -> Maybe (MinMaxMeanVar n)
mmmv = fmap simpleStatDesc . tangibleRandomness
{-# SPECIALIZE mmmv :: (DelayModel d Double, SimpleStatDesc d Double) =>
                        DeltaQ Rational d Double -> Maybe (MinMaxMeanVar Double) #-}

-- | The loss probability for a given ∆Q
lossprob :: (Fractional p, Real p, DelayModel d n) => DeltaQ p d n -> Double
lossprob = fromRational . (flip subtract 1) . toRational . tangibleMass
