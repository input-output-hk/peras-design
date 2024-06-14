{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Peras.Markov.PolynomialSpec where

import NumericPrelude.Base
import NumericPrelude.Numeric

import Control.Applicative (pure, (<*>))
import Control.Arrow (Arrow (second, (***)))
import Data.Functor ((<$>))
import Number.Ratio ((%))
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
  let check description generator comparator =
        describe description $
          do
            it "Monomials" $
              property $
                forAll ((,) <$> generator <*> genMonomial) $ \((p, q), (concrete, symbolic)) ->
                  counterexample ("Polynomial: " <> show (pretty symbolic)) $
                    evalMonomial p q symbolic `comparator` concrete p q
            it "Terms" $
              property $
                forAll ((,) <$> generator <*> (second (uncurry MkTerm) <$> genTerm)) $ \((p, q), (concrete, symbolic)) ->
                  counterexample ("Polynomial: " <> show (pretty symbolic)) $
                    evalTerm p q symbolic `comparator` concrete p q
            it "Polynomials" $
              property $
                forAll ((,) <$> generator <*> genPolynomial) $ \((p, q), (concrete, symbolic)) ->
                  counterexample ("Polynomial: " <> show (pretty symbolic)) $
                    eval p q symbolic `comparator` concrete p q
            it "Addition" $
              property $
                forAll ((,,) <$> generator <*> genPolynomial <*> genPolynomial) $ \((p, q), (concrete, symbolic), (concrete', symbolic')) ->
                  counterexample ("Polynomials: " <> show (pretty symbolic <+> pretty "&" <+> pretty symbolic')) $
                    let actual = eval p q $ symbolic + symbolic'
                        expected = concrete p q + concrete' p q
                     in actual `comparator` expected
            it "Multiplication" $
              property $
                forAll ((,,) <$> generator <*> genPolynomial <*> genPolynomial) $ \((p, q), (concrete, symbolic), (concrete', symbolic')) ->
                  counterexample ("Polynomials: " <> show (pretty symbolic <+> pretty "&" <+> pretty symbolic')) $
                    let actual = eval p q $ symbolic * symbolic'
                        expected = concrete p q * concrete' p q
                     in actual `comparator` expected
  check "Polynomial arithmetic identical to rational arithmetic" genRationalPQ shouldBe
  check "Polynomial arithmetic identical to floating-point arithmetic" genDoublePQ shouldBeApproximately

shouldBeApproximately :: Double -> Double -> Expectation
shouldBeApproximately x y = abs (x - y) `shouldSatisfy` (< 1e-9)

genRationalPQ :: Gen (Rational, Rational)
genRationalPQ =
  do
    p <- do
      d <- choose (1, 1000000)
      n <- choose (0, d)
      pure $ n % d
    pure (p, 1 - p)

genDoublePQ :: Gen (Double, Double)
genDoublePQ =
  do
    p <- choose (0, 1)
    pure (p, 1 - p)

instance Show (a -> a -> a) where
  show _ = "<<a function>>"

genMonomial :: Ring.C a => Gen (a -> a -> a, Monomial)
genMonomial =
  do
    i <- choose (0, 5)
    j <- choose (0, 5)
    pure (\p q -> p ^ toInteger i * q ^ toInteger j, MkMonomial i j)

genTerm :: (Arbitrary a, Ring.C a) => Gen (a -> a -> a, (Monomial, a))
genTerm =
  do
    c <- arbitrary
    ((\f p q -> c * f p q) *** (,c)) <$> genMonomial

genPolynomial :: (Arbitrary a, Ring.C a) => Gen (a -> a -> a, Polynomial a)
genPolynomial =
  ((\fs p q -> sum $ (\f -> f p q) <$> fs) *** MkPolynomial . Map.fromListWith (+)) . unzip <$> listOf genTerm
