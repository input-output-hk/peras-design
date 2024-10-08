{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Peras.Markov.Polynomial (
  Monomial (..),
  Term (..),
  Polynomial (..),
  num,
  p,
  q,
  eval,
  evalMonomial,
  evalTerm,
  evaluate,
) where

import NumericPrelude.Base
import NumericPrelude.Numeric

import Control.Applicative ((<$>), (<*>))
import Data.Function (on)
import Data.Map.Strict (Map)
import Prettyprinter (Pretty (pretty), concatWith, (<+>), (<>))
import Test.QuickCheck

import qualified Algebra.Additive as Additive (C)
import qualified Algebra.Ring as Ring (C)
import qualified Data.Map.Strict as Map (empty, filter, foldlWithKey', fromList, map, mapKeys, null, singleton, toList, unionWith)

data Monomial = MkMonomial
  { pDegree :: Int
  , qDegree :: Int
  }
  deriving (Eq, Read, Show)

instance Ord Monomial where
  compare = on compare $ \MkMonomial{pDegree, qDegree} -> (pDegree + qDegree, qDegree - pDegree)

instance Additive.C Monomial where
  zero = MkMonomial 0 0
  x + y = MkMonomial (on (+) pDegree x y) (on (+) qDegree x y)
  x - y = MkMonomial (on (-) pDegree x y) (on (-) qDegree x y)

instance Arbitrary Monomial where
  arbitrary = MkMonomial <$> choose (0, 5) <*> choose (0, 5)

instance Pretty Monomial where
  pretty = \case
    MkMonomial 0 0 -> pretty "1"
    MkMonomial 1 0 -> pretty "p"
    MkMonomial 0 1 -> pretty "q"
    MkMonomial m 0 -> pretty $ "p" <> toSuperscript m
    MkMonomial 0 n -> pretty $ "q" <> toSuperscript n
    MkMonomial 1 1 -> pretty "p⋅q"
    MkMonomial 1 n -> pretty $ "p⋅q" <> toSuperscript n
    MkMonomial m 1 -> pretty $ "p" <> toSuperscript m <> "⋅q"
    MkMonomial m n -> pretty $ "p" <> toSuperscript m <> "⋅q" <> toSuperscript n
   where
    super :: Char -> Char
    super '0' = '⁰'
    super '1' = '¹'
    super '2' = '²'
    super '3' = '³'
    super '4' = '⁴'
    super '5' = '⁵'
    super '6' = '⁶'
    super '7' = '⁷'
    super '8' = '⁸'
    super '9' = '⁹'
    super x = x
    toSuperscript :: Int -> String
    toSuperscript x
      | x < 0 = "⁻" <> (super <$> show x)
      | x == 0 = ""
      | otherwise = super <$> show x

data Term a = MkTerm
  { monomial :: Monomial
  , coefficient :: a
  }
  deriving (Eq, Ord, Read, Show)

instance (Eq a, Ring.C a, Pretty a) => Pretty (Term a) where
  pretty MkTerm{coefficient, monomial}
    | monomial == zero = pretty coefficient
    | coefficient == one = pretty monomial
    | otherwise = pretty coefficient <> pretty "⋅" <> pretty monomial

instance Arbitrary a => Arbitrary (Term a) where
  arbitrary = MkTerm <$> arbitrary <*> arbitrary

newtype Polynomial a = MkPolynomial
  { terms :: Map Monomial a
  }
  deriving stock (Eq, Ord, Read, Show)

instance Functor Polynomial where
  fmap f = MkPolynomial . Map.map f . terms

instance (Eq a, Additive.C a) => Additive.C (Polynomial a) where
  zero = canonical Map.empty
  x + y = canonical $ on (Map.unionWith (+)) terms x y
  x - y = canonical $ on (Map.unionWith (-)) terms x y

instance (Eq a, Ring.C a) => Ring.C (Polynomial a) where
  one = num one
  fromInteger = canonical . Map.singleton zero . fromInteger
  (*) x = canonical . Map.foldlWithKey' (flip (flip . (Map.unionWith (+) .) . mul)) Map.empty . terms
   where
    mul ym yc = Map.mapKeys (ym +) . Map.map (yc *) $ terms x

instance Arbitrary a => Arbitrary (Polynomial a) where
  arbitrary = MkPolynomial . Map.fromList <$> arbitrary

instance (Eq a, Ring.C a, Pretty a) => Pretty (Polynomial a) where
  pretty MkPolynomial{terms}
    | Map.null terms = pretty "0"
    | otherwise = concatWith (\x y -> x <+> pretty "+" <+> y) . fmap (pretty . uncurry MkTerm) $ Map.toList terms

canonical :: (Eq a, Additive.C a) => Map Monomial a -> Polynomial a
canonical = MkPolynomial . Map.filter (/= zero)

num :: Additive.C a => a -> Polynomial a
num = MkPolynomial . Map.singleton zero

p :: Ring.C a => Polynomial a
p = MkPolynomial $ MkMonomial one zero `Map.singleton` one

q :: Ring.C a => Polynomial a
q = MkPolynomial $ MkMonomial zero one `Map.singleton` one

evalMonomial :: Ring.C a => a -> a -> Monomial -> a
evalMonomial p' q' MkMonomial{pDegree, qDegree} = p' ^ toInteger pDegree * q' ^ toInteger qDegree

evalTerm :: Ring.C a => a -> a -> Term a -> a
evalTerm p' q' MkTerm{monomial, coefficient} = coefficient * evalMonomial p' q' monomial

eval :: Ring.C a => a -> a -> Polynomial a -> a
eval p' q' = sum . fmap (evalTerm p' q' . uncurry MkTerm) . Map.toList . terms

evaluate :: (Functor t, Ring.C a) => a -> a -> t (Polynomial a) -> t a
evaluate = (fmap .) . eval
