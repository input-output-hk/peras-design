{-# LANGUAGE LambdaCase #-}

module DeltaQ.Numeric.CDF (
    module DeltaQ.Numeric.CDF.Types,
    empiricalCDF,
    sampleDeltaQ,
)
where

import Control.Monad
import Control.Monad.Primitive
import Statistics.Distribution
import Statistics.Distribution.Uniform
import System.Random.MWC
import System.Random.MWC.Distributions

import DeltaQ.Numeric.CDF.Types
import DeltaQ.RationalProbabilityDoubleDelay

{- | Evaluate (with n steps) the empirical improper CDF. Requires a
  generator.
-}
empiricalCDF ::
    (PrimMonad m) =>
    Gen (PrimState m) ->
    Int ->
    DeltaQ ->
    m EmpiricalCDF
empiricalCDF gen n dq =
    fmap makeEmpiricalCDF . replicateM n $ sampleDeltaQ gen dq

-- | take a single sampled from an improper random variable.
sampleDeltaQ ::
    (PrimMonad m) =>
    Gen (PrimState m) ->
    DeltaQ ->
    m (Maybe Double)
sampleDeltaQ gen = \case
    (Delay (DiracDelta t)) ->
        return $ Just t
    (Delay (UniformD t)) ->
        fmap Just $ genContVar (uniformDistr 0 t) gen
    (ProbChoice p a b) -> do
        weightedChoice >>= sampleDeltaQ gen
      where
        weightedChoice = do
            t <- bernoulli (fromRational p) gen
            return $ if t then a else b
    (Convolve a b) -> do
        a' <- sampleDeltaQ gen a
        b' <- sampleDeltaQ gen b
        case (a', b') of
            (Just a'', Just b'') ->
                return $ Just (a'' + b'')
            _ -> return Nothing
    Bottom ->
        return Nothing
    Unit ->
        return $ Just 0
