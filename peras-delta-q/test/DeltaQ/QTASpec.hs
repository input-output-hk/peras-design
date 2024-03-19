module DeltaQ.QTASpec where

import A (CDF (..), tabulate, toCDF)
import Control.Monad (foldM)
import Data.Function ((&))
import Data.List (find)
import Data.List.NonEmpty (NonEmpty ((:|)), fromList, toList)
import qualified Data.List.NonEmpty as NE
import Data.Maybe (fromMaybe)
import Data.Ratio ((%))
import Debug.Trace (trace)
import DeltaQ.QTA (fromQTA)
import NumericalCDF (NCDF)
import Peras (toI)
import Test.Hspec (Spec, describe)
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (Arbitrary (..), Positive (..), Property, Small (..), Testable (..), choose, counterexample, forAll, sized, suchThat)
import UnitInterval (Iops, one)

spec :: Spec
spec =
  describe "From QTA" $ do
    prop "derives A-expression from valid QTA series" $ prop_derivesExpressionFromQTA

newtype QTA = QTA (NonEmpty (Double, Double))
  deriving (Eq, Show)

instance Arbitrary QTA where
  arbitrary = do
    Positive (Small n) <- arbitrary
    incr <- choose (0.1, 10.0)
    let len = n + 1
    pure $
      QTA $
        ( \i ->
            ( fromRational $ 1 % fromIntegral len
            , fromIntegral i * incr
            )
        )
          <$> (fromList [1 .. len])

-- | Provides an interval of cumulative probabilities for a given real value.
probability :: (CDF t, Iops (I t), Ord (R t)) => t -> R t -> R t -> I t
probability cdf dx v =
  let table = tabulate cdf dx
   in snd $ last $ takeWhile ((v >) . fst) table

prop_derivesExpressionFromQTA :: QTA -> Property
prop_derivesExpressionFromQTA (QTA qta) =
  let cdf = toCDF @NCDF (fromQTA qta) dx
      dx = 1 / 1000
      maxv = maxx cdf
   in forAll (choose (0, maxv)) $ \v ->
        let proba = probability cdf dx v
            expected = cumulativeProba v qta
         in property (proba == expected)
              & counterexample ("expected: " <> show expected)
              & counterexample ("proba: " <> show proba)
              & counterexample ("cdf: " <> show (tabulate cdf dx))

cumulativeProba :: Double -> NonEmpty (Double, Double) -> Double
cumulativeProba v qta =
  let (sup, rest) = NE.span ((v >) . snd) qta
   in sum $ map fst $ sup <> [head rest]
