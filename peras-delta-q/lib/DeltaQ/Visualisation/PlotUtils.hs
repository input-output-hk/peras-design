module DeltaQ.Visualisation.PlotUtils
  ( DelayExtension(..)
  , PlotInfo(..)
  , defaultPlotInfo
  , toPlottableCDF
  , toPlottableCDF'
  )
where

import Control.Monad
import Control.Monad.IO.Class
import Data.List
import Data.Maybe
import DeltaQ.Numeric.CDF
import DeltaQ.RationalProbabilityDoubleDelay
import System.Random.MWC


data DelayExtension delay
  = NoDelayExtension
  | AbsoluteDelay delay
  | AbsoluteDelayExtension delay
  | RelativeDelayExtension delay
  deriving (Show)


data PlotInfo delay
  = PI { _noSamples :: Int
       , _maxDelay  :: DelayExtension delay
       }

defaultPlotInfo :: PlotInfo delay
defaultPlotInfo = PI 1000 NoDelayExtension

-- | Generate a CDF plot by Monte-Carlo evaluation of the given
--   `DeltaQ`. The number of samples for the plot is the number of
--   samples taken from the supporting improper random variable. Uses
--   the syntatic structure to evaluate the tangible mass in the
--   distribution.
toPlottableCDF' :: (MonadIO m)
                => PlotInfo Double
                -> GenIO
                -> DeltaQ
                -> m [(Double, Double)]
toPlottableCDF'  (PI np de) gen dq =
    fmap f . replicateM np . liftIO $ sampleDeltaQ gen dq
  where
    f :: [Maybe Double] -> [(Double, Double)]
    f = (applyDelayExtension de)
        . (map (\(a,b) -> (a, fromRational b)))
        . (asCDF np)
    asCDF n xs
      = (0,0) : zip (sort $ catMaybes xs) cs
      where
        cs = map ( / fromIntegral n) $ iterate (+1) 1

toPlottableCDF :: (MonadIO m)
               => GenIO
               -> DeltaQ
               -> m [(Double, Double)]
toPlottableCDF = toPlottableCDF' defaultPlotInfo

-- | Optionall construct an additional horizontal line for the right
--   hand side of the delay Numericall CDF
applyDelayExtension :: (Num delay, Ord delay)
                    => DelayExtension delay
                    -> [(delay, t)]
                    -> [(delay, t)]
applyDelayExtension NoDelayExtension zs
  = zs
applyDelayExtension (AbsoluteDelay x) zs
  | null zs
    = zs
  | l'x > x
    = zs
  | otherwise
    = zs ++ [(x, l'y)]
  where
    (l'x, l'y) = last zs
applyDelayExtension (AbsoluteDelayExtension x) zs
  | null zs
    = zs
  | otherwise
    = zs ++ [(l'x + x , l'y)]
  where
    (l'x, l'y) = last zs
applyDelayExtension (RelativeDelayExtension x) zs
  | null zs
    = zs
  | otherwise
    = zs ++ [(l'x * (1 + x) , l'y)]
  where
    (l'x, l'y) = last zs
