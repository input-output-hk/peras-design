{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Peras.Markov.Adversary.CommonCandidateSpec where

import NumericPrelude.Base
import NumericPrelude.Numeric hiding (sum)
import Prelude (sum)

import Control.Applicative (pure, (<*>))
import Control.Arrow (Arrow (second, (***)))
import Control.Monad (zipWithM_)
import Data.Default (def)
import Data.Functor ((<$>))
import Data.Maybe (fromMaybe)
import Number.Ratio ((%))
import Peras.Markov.Adversary (transitions)
import Peras.Markov.Adversary.CommonCandidate (Divergence (lengths), scenario, separatedChains)
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
import Statistics.Distribution (probability)
import Statistics.Distribution.Binomial (binomial)
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
spec = describe "Separated chains" $
  do
    it "Probabilities sum to unity" $
      property $
        forAll ((,) <$> genLimit <*> genPQ) $ \(n, (p, q)) -> do
          let result = transitions p q n separatedChains def
          sum result `shouldBeApproximately` 1
    it "Probabilities match theory" $
      property $
        forAll ((,) <$> genLimit <*> genPQ) $ \(n, (p, q)) -> do
          let result = transitions p q n separatedChains def
              actual = [fromMaybe 0 $ (i, j) `Map.lookup` lengths result | i <- [0 .. n], j <- [0 .. n]]
              expected =
                [ probability pd i * probability qd j
                | let pd = binomial n p
                , let qd = binomial n q
                , i <- [0 .. n]
                , j <- [0 .. n]
                ]
          counterexample ("Lengths: " <> show [(i, j) | i <- [0 .. n], j <- [0 .. n]])
            . counterexample ("Expected: " <> show expected)
            . counterexample ("Actual: " <> show actual)
            $ zipWithM_ shouldBeApproximately actual expected
    it "Scenario probabilities sum to unity" $
      property $
        forAll ((,,) <$> genLimit <*> genLimit <*> genPQ) $ \(u, l, (p, q)) -> do
          let n = u + l
              (result, noBlocks) = scenario u l p q
          (sum result + noBlocks) `shouldBeApproximately` 1
    it "Scenario matches theory" $
      property $
        forAll ((,,) <$> genLimit <*> genLimit <*> genPQ) $ \(u, l, (p, q)) -> do
          let n = u + l
              result = fst $ scenario u l p q
              actual = [fromMaybe 0 $ (i, j) `Map.lookup` lengths result | i <- [0 .. n], j <- [0 .. n]]
              expected =
                [ probability pd i
                  * sum
                    [ probability qud ju * probability qld jl
                    | ju <- [1 .. u]
                    , jl <- [0 .. l]
                    , ju + jl == j
                    ]
                | let pd = binomial n p
                , let qud = binomial u q
                , let qld = binomial l q
                , i <- [0 .. n]
                , j <- [0 .. n]
                ]
          counterexample ("Lengths: " <> show [(i, j) | i <- [0 .. n], j <- [0 .. n]])
            . counterexample ("Expected: " <> show expected)
            . counterexample ("Actual: " <> show actual)
            $ zipWithM_ shouldBeApproximately actual expected

shouldBeApproximately :: Double -> Double -> Expectation
shouldBeApproximately x y = abs (x - y) `shouldSatisfy` (<= (1e-9 * abs (x + y)))

genPQ :: Gen (Double, Double)
genPQ =
  do
    p <- choose (0, 1)
    q <- choose (0, 1 - p)
    pure (p, 1 - p)

genLimit :: Gen Int
genLimit = choose (0, 30)
