{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Peras.Markov.Adversary.CommonCandidate (
  Divergence (..),
  summarize,
  separatedChains,
  scenario,
) where

import NumericPrelude.Base
import NumericPrelude.Numeric

import Data.Default (Default (def))
import Data.Foldable (Foldable)
import Data.Functor ((<$>))
import Data.Map (Map)
import Peras.Markov.Adversary (transitions)
import Prettyprinter (Doc, Pretty (pretty), fill, vsep, (<+>), (<>))

import qualified Algebra.Additive as Additive (C)
import qualified Algebra.Ring as Ring (C)
import qualified Data.Map.Strict as Map

newtype Divergence a = MkDivergence
  { lengths :: Map (Int, Int) a
  }
  deriving stock (Eq, Ord, Read, Show)

instance Functor Divergence where
  fmap f = MkDivergence . Map.map f . lengths

instance Foldable Divergence where
  foldr = flip flip lengths . ((.) .) . Map.foldr'

instance Ring.C a => Default (Divergence a) where
  def = MkDivergence $ Map.singleton (0, 0) one

instance (Eq a, Ring.C a, Pretty a) => Pretty (Divergence a) where
  pretty MkDivergence{lengths} =
    let pretty' ((lHonest, lAdversary), polynomial) = fill 15 (pretty lHonest) <+> fill 19 (pretty lAdversary) <+> pretty polynomial
        header =
          [ fill 15 (pretty "Honest length") <+> fill 19 (pretty "Adversary length") <+> pretty "Probability"
          , fill 15 (pretty "-------------") <+> fill 19 (pretty "----------------") <+> pretty "-----------"
          ]
        rows = pretty' <$> Map.toList lengths
     in vsep $ header <> rows

summarize :: (Additive.C a, Pretty a) => Divergence a -> Doc ann
summarize MkDivergence{lengths} =
  let
    summary = Map.mapKeysWith (+) (uncurry compare) lengths
    pretty' (cmp, polynomial) = fill 30 (pretty $ show cmp <> " & adversary candidate") <+> pretty polynomial
    header =
      [ fill 30 (pretty "Honest vs adversary length") <+> pretty "Probability"
      , fill 30 (pretty "--------------------------") <+> pretty "-----------"
      ]
    rows = pretty' <$> Map.toList summary
   in
    vsep $ header <> rows

transitionImpl :: Ring.C a => (a -> a -> (Int, Int) -> Map (Int, Int) a) -> a -> a -> Divergence a -> Divergence a
transitionImpl transition' p q =
  MkDivergence
    . Map.foldlWithKey' (\acc delta weight -> Map.unionWith (+) (Map.map (* weight) $ transition' p q delta) acc) Map.empty
    . lengths

separatedChains :: Ring.C a => a -> a -> Divergence a -> Divergence a
separatedChains =
  transitionImpl $ \p q (lHonest, lAdversary) ->
    Map.fromList
      [ ((lHonest + 1, lAdversary), p * (one - q)) -- Honest party lengthens their chain.
      , ((lHonest, lAdversary + 1), (one - p) * q) -- Adversary lengthens their chain.
      , ((lHonest + 1, lAdversary + 1), p * q) -- Both parties lengthen their chains.
      , ((lHonest, lAdversary), (one - p) * (one - q)) -- Neither party lengthens their chain.
      ]

-- | Find the distribution of chain lengths after U + L slots, given
-- that an adversarial block has been produced in the first U slots.
scenario ::
  Ring.C a =>
  -- | Peras U
  Int ->
  -- | Peras L
  Int ->
  -- | Probability of honest block
  a ->
  -- | Probability of adversarial block
  a ->
  -- | Joint distribution of chain lengths and the probability that the adversary didn't produce a block in the first U slots.
  (Divergence a, a)
scenario perasU perasL p q =
  let
    -- Run the chains forward U slots.
    interim = transitions p q perasU separatedChains def
    -- Discard chains that have not produced an adversary block yet.
    interimWithAdversarialBlock = MkDivergence . Map.filterWithKey (const . (/= 0) . snd) $ lengths interim
    noBlock = Map.foldrWithKey (\k v acc -> if snd k == 0 then acc + v else acc) zero $ lengths interim
    -- Run the chains forward K slots.
    result = transitions p q perasL separatedChains interimWithAdversarialBlock
   in
    (result, noBlock)
