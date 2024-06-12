{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Peras.Markov.Adversary where

import NumericPrelude.Base
import NumericPrelude.Numeric

import Data.Default (Default (def))
import Data.Foldable (toList)
import Data.Function (on)
import Data.Functor ((<$>))
import Data.IntMap (IntMap)
import Data.List (sortBy)
import Number.Ratio (T ((:%)))
import Peras.Markov.Polynomial (Polynomial, eval, num)
import Prettyprinter (Pretty (pretty), fill, vsep, (<+>), (<>))

import qualified Algebra.Absolute as Absolute (C)
import qualified Algebra.Additive as Additive (C)
import qualified Algebra.Field as Field (C)
import qualified Algebra.Ring as Ring (C)
import qualified Data.IntMap.Strict as Map (empty, foldrWithKey', fromList, lookup, map, singleton, toList, unionWith)

newtype Deltas a = MkDeltas
  { -- FIXME: Also track the total number of transitions.
    deltas :: IntMap a
  }
  deriving (Eq, Functor, Ord, Read, Show)

instance (Eq a, Ring.C a) => Default (Deltas a) where
  def = MkDeltas $ Map.singleton 0 one

instance (Eq a, Ring.C a, Pretty a) => Pretty (Deltas a) where
  pretty MkDeltas{deltas} =
    let pretty' (delta, polynomial) = fill 10 (pretty delta) <+> pretty polynomial
        header =
          [ fill 10 (pretty "Delta") <+> pretty "Probability"
          , fill 10 (pretty "-----") <+> pretty "-----------"
          ]
        rows = pretty' <$> Map.toList deltas
     in vsep $ header <> rows

lookupDelta :: Int -> Deltas a -> Maybe a
lookupDelta = (. deltas) . Map.lookup

type DoubleDeltas = Deltas Double

type RationalDeltas = Deltas Rational

type DoublePolynomialDeltas = Deltas (Polynomial Double)

type RationalPolynomialDeltas = Deltas (Polynomial Rational)

instance Pretty Rational where
  pretty (n :% 1) = pretty n
  pretty (n :% d) = pretty $ show n <> "/" <> show d

class Half a where
  half :: a

instance Half Double where
  half = 1 / 2

instance Half Rational where
  half = 1 % 2

instance Field.C a => Half (Polynomial a) where
  half = num $ one / (one + one)

transitions :: a -> a -> Int -> (a -> a -> Deltas a -> Deltas a) -> Deltas a -> Deltas a
transitions p q n transition' initial = foldr id initial . replicate n $ transition' p q

transitionImpl :: Additive.C a => (a -> a -> Int -> a -> IntMap a) -> a -> a -> Deltas a -> Deltas a
transitionImpl transition' p q = MkDeltas . Map.foldrWithKey' ((Map.unionWith (+) .) . transition' p q) Map.empty . deltas

evaluate :: Ring.C a => a -> a -> Deltas (Polynomial a) -> Deltas a
evaluate p q = MkDeltas . Map.map (eval p q) . deltas

sumProbabilities :: (Absolute.C a, Additive.C a, Ord a) => Deltas a -> a
sumProbabilities = sum . sortBy (compare `on` abs) . toList . deltas

separatedChains :: Ring.C a => a -> a -> Deltas a -> Deltas a
separatedChains =
  transitionImpl $ \p q delta weight ->
    -- FIXME: Handle case where both honest and adversarial parties produce a block in the same slot.
    Map.fromList
      [ (delta + 1, p * weight) -- Honest party builds their own chain.
      , (delta - 1, q * weight) -- Adversary builds their own separate chain.
      ]

splitChains :: (Half a, Ring.C a) => a -> a -> Deltas a -> Deltas a
splitChains =
  transitionImpl $ \p q delta weight ->
    -- FIXME: Handle case where both honest and adversarial parties produce a block in the same slot.
    case compare delta zero of
      LT ->
        Map.fromList
          [ (delta - 1, p * weight) -- Honest party lengthens the longer chain.
          , (delta + 1, q * weight) -- Adversary lengthens the shorter chain.
          ]
      GT ->
        Map.fromList
          [ (delta + 1, p * weight) -- Honest party lengthens the longer chain.
          , (delta - 1, q * weight) -- Adversary lengthens the shorter chain.
          ]
      EQ ->
        Map.fromList
          [ (delta + 1, half * weight) -- No preference by either party.
          , (delta - 1, half * weight) -- No preference by either party.
          ]
