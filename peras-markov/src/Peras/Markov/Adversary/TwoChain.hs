{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Peras.Markov.Adversary.TwoChain (
  Deltas (..),
  lookupDelta,
  separatedChains,
  splitChains,
) where

import NumericPrelude.Base
import NumericPrelude.Numeric

import Data.Default (Default (def))
import Data.Foldable (Foldable)
import Data.Functor ((<$>))
import Data.IntMap (IntMap)
import Peras.Markov.Class (Half (half))
import Prettyprinter (Pretty (pretty), fill, vsep, (<+>), (<>))

import qualified Algebra.Additive as Additive (C)
import qualified Algebra.Ring as Ring (C)
import qualified Data.IntMap.Strict as Map (empty, foldlWithKey', foldr', fromList, lookup, map, singleton, toList, unionWith)

newtype Deltas a = MkDeltas
  { -- FIXME: Also track the total number of transitions.
    deltas :: IntMap a
  }
  deriving stock (Eq, Ord, Read, Show)

instance Functor Deltas where
  fmap f = MkDeltas . Map.map f . deltas

instance Foldable Deltas where
  foldr = flip flip deltas . ((.) .) . Map.foldr'

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

transitionImpl :: Additive.C a => (a -> a -> Int -> a -> IntMap a) -> a -> a -> Deltas a -> Deltas a
transitionImpl transition' p q = MkDeltas . Map.foldlWithKey' (flip (flip . (Map.unionWith (+) .) . transition' p q)) Map.empty . deltas

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
