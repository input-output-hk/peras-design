module Data.Statistics.Util where

-- | Check whether a value falls within the central portion of a binomial distribution.
equalsBinomialWithinTails ::
  -- | The sample size.
  Int ->
  -- | The binomial propability.
  Double ->
  -- | The number of sigmas that define the central acceptance portion.
  Double ->
  -- | The actual observation.
  Int ->
  -- | Whether the observation falls within the central region.
  Bool
equalsBinomialWithinTails trials probability sigmas actual =
  equalsNormalWithinTails
    (fromIntegral trials * probability)
    (fromIntegral trials * probability * (1 - probability))
    sigmas
    (fromIntegral actual)

-- | Check whether a value falls within the central portion of a normal distribution.
equalsNormalWithinTails ::
  -- | The mean.
  Double ->
  -- | The variance.
  Double ->
  -- | The number of sigmas that define the central acceptance portion.
  Double ->
  -- | The actual observation.
  Double ->
  -- | Whether the observation falls within the central region.
  Bool
equalsNormalWithinTails mean variance sigmas actual =
  let
    spread = sigmas * sqrt variance
   in
    mean - spread <= actual && actual <= mean + spread
