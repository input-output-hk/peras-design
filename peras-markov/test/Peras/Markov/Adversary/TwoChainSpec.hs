{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Peras.Markov.Adversary.TwoChainSpec where

import NumericPrelude.Base
import NumericPrelude.Numeric

import Control.Applicative (pure, (<*>))
import Control.Arrow (Arrow (second, (***)))
import Control.Monad (zipWithM_)
import Data.Default (def)
import Data.Functor ((<$>))
import Data.Maybe (fromMaybe)
import Debug.Trace
import Number.Ratio ((%))
import Peras.Markov.Adversary
import Peras.Markov.Adversary.TwoChain
import Peras.Markov.Orphans ()
import Peras.Markov.Polynomial (
  Monomial (MkMonomial),
  Polynomial (MkPolynomial),
  Term (MkTerm),
  eval,
  evalMonomial,
  evalTerm,
 )
import Prettyprinter (Pretty (pretty), (<+>), (<>))
import Statistics.Distribution
import Statistics.Distribution.Binomial
import Test.Hspec (Expectation, Spec, describe, it, shouldBe, shouldSatisfy)
import Test.QuickCheck (
  Arbitrary (arbitrary),
  Gen,
  Testable (property),
  choose,
  counterexample,
  forAll,
  listOf,
 )

import qualified Algebra.Absolute as Absolute (C)
import qualified Algebra.Ring as Ring (C)
import qualified Data.Map.Strict as Map

spec :: Spec
spec = do
  describe "Separated chains" $
    do
      it "Probabilities sum to unity" $
        property $
          forAll ((,) <$> genLimit <*> genPQ) $ \(n, (p, q)) -> do
            let result = transitions p q n separatedChains def
                actual = [fromMaybe 0 $ lookupDelta delta result | delta <- [-n .. n]]
            sum actual `shouldBeApproximately` 1
      it "Probabilities match theory" $
        property $
          forAll ((,) <$> genLimit <*> genPQ) $ \(n, (p, q)) -> do
            let result = transitions p q n separatedChains def
                actual = [fromMaybe 0 $ lookupDelta delta result | delta <- [-n .. n]]
                expected =
                  [ sum
                    [ probability pd i * probability qd j
                    | i <- [0 .. n]
                    , let j = i - delta
                    , 0 <= j && j <= n
                    ]
                  | let pd = binomial n p
                  , let qd = binomial n q
                  , delta <- [-n .. n]
                  ]
            counterexample ("Deltas: " <> show [-n .. n])
              . counterexample ("Expected: " <> show expected)
              . counterexample ("Actual: " <> show actual)
              $ zipWithM_ shouldBeApproximately actual expected
  describe "Split chains" $
    do
      it "Probabilities sum to unity" $
        property $
          forAll ((,) <$> genLimit <*> genPQ) $ \(n, (p, q)) -> do
            let result = transitions p q n splitChains def
                actual = [fromMaybe 0 $ lookupDelta delta result | delta <- [-n .. n]]
            sum actual `shouldBeApproximately` 1

shouldBeApproximately :: Double -> Double -> Expectation
shouldBeApproximately x y = abs (x - y) `shouldSatisfy` (< (1e-9 * abs (x + y)))

genPQ :: Gen (Double, Double)
genPQ =
  do
    p <- choose (0, 1)
    pure (p, 1 - p)

genLimit :: Gen Int
genLimit = choose (0, 30)
