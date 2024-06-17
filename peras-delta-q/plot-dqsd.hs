{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

import Control.Monad (void)
import Data.Ratio
import Debug.Trace (trace)
import DeltaQ.Model.DeltaQ (DeltaQOps (..), convolve)
import DeltaQ.Model.Utilities (plotCDFs)
import DeltaQ.PWPs (IRV, asDiscreteCDF, fromQTA, uniform0)
import GHC.Stack (HasCallStack)
import Graphics.Rendering.Chart.Backend.Cairo (FileFormat (SVG), FileOptions (_fo_format), renderableToFile)
import Graphics.Rendering.Chart.Easy (def, layoutToRenderable)
import PWPs.IRVs (makeCDF)

main :: IO ()
main = do
  -- oneHop
  -- hopsDistribution 5
  -- hopsProbability
  void networkWithCertsProbability

oneMTU =
  fromQTA @(IRV Double)
    [(0.012, fromRational $ 1 % 3), (0.069, fromRational $ 2 % 3), (0.268, fromRational $ 3 % 3)]
blockBody64K =
  fromQTA
    [(0.024, fromRational $ 1 % 3), (0.143, fromRational $ 2 % 3), (0.531, fromRational $ 3 % 3)]
headerRequestReply = oneMTU `convolve` oneMTU -- request/reply
bodyRequestReply = oneMTU `convolve` blockBody64K -- request/reply
oneBlockDiffusion = headerRequestReply `convolve` bodyRequestReply

certRequestReply = oneMTU `convolve` oneMTU -- request/reply
certValidation = uniform0 0.050
certHandling = certRequestReply `convolve` certValidation
headerWithCert = choice (fromRational $ 1 % 3) (headerRequestReply `convolve` certHandling) headerRequestReply
certBlockOneThird = headerWithCert `convolve` bodyRequestReply
certBlockAll = headerRequestReply `convolve` certHandling `convolve` bodyRequestReply

combine = nWayChoice
multiHop :: (DeltaQOps icdf, Show icdf) => Int -> icdf -> icdf
multiHop n dq = nWayConvolve $ replicate n dq

multihops = (`multiHop` oneBlockDiffusion) <$> [1 ..]

-- model for average degree 15
pathLengthsDistributionDegree15 =
  [0.60, 8.58, 65.86 + 24.95]
hopsProba15 = zip (scanl1 (+) pathLengthsDistributionDegree15) multihops
deltaq15 = combine hopsProba15

-- model for average degree 10
pathLengthsDistributionDegree10 =
  [0.40, 3.91, 31.06, 61.85, 2.78]
hopsProba10 = zip (scanl1 (+) pathLengthsDistributionDegree10) multihops
deltaq10 = combine hopsProba10

certAllDeltaQ15 =
  combine $ zip (scanl1 (+) pathLengthsDistributionDegree10) $ (`multiHop` certBlockAll) <$> [1 ..]
certOneThirdDeltaQ15 =
  combine $ zip (scanl1 (+) pathLengthsDistributionDegree10) $ (`multiHop` certBlockOneThird) <$> [1 ..]

networkWithCertsProbability =
  renderableToFile def{_fo_format = SVG} "network-with-cert.svg" $ do
    layoutToRenderable $
      plotCDFs
        "Peras Network Diffusion (δ=15)"
        [("diffusion", deltaq15)]

-- -- layout_title .= "Peras Network Diffusion (δ=15)"
-- -- layout_x_axis . laxis_title .= "time (seconds)"
-- -- layout_y_axis . laxis_title .= "probability (cumul.)"
-- -- plot (line "block diffusion w/o cert" [cdf15Data])
-- -- plot (line "block diffusion w/ cert" [certAllData])
-- -- plot (line "95%" [[(0.0, 0.95), (6.0, 0.95)]])

-- hopsProbability = do
--   gen <- createSystemRandom
--   cdf15 <- empiricalCDF gen 500 deltaq15
--   cdf10 <- empiricalCDF gen 500 deltaq10
--   let samples = fromRational . (% 1000) <$> [0 .. 5000]
--       cdf15Data = zip samples (fromRational @Double . _ecdf cdf15 <$> samples)
--       cdf10Data = zip samples (fromRational @Double . _ecdf cdf10 <$> samples)

--   toFile def{_fo_format = SVG} "peras.svg" $ do
--     layout_title .= "Praos Network Diffusion"
--     plot (line "block diffusion (δ=15)" [cdf15Data])
--     plot (line "block diffusion (δ=10)" [cdf10Data])
--     plot (line "95%" [[(0.0, 0.95), (5.0, 0.95)]])

-- hopsDistribution n = do
--   let hops = [1 .. n]
--   gen <- createSystemRandom
--   hopsCDF <- forM hops $ \n -> empiricalCDF gen 500 (n `multiHop` oneBlockDiffusion)
--   let samples = fromRational . (% 1000) <$> [0 .. 5000]

--       loop acc h =
--         try (hGetLine h) >>= \case
--           Left (_ :: IOException) -> pure $ reverse acc
--           Right line ->
--             let l = bimap ((/ 100) . read) read $ break (== '\t') line
--              in loop (l : acc) h

--   mainnet :: [(Double, Double)] <- withFile "block-diffusion" ReadMode $ loop []

--   toFile def{_fo_format = SVG} "praos-multi-hops.svg" $ do
--     layout_title .= "Praos Multi-Hops Block diffusion"
--     forM_ hops $ \n ->
--       plot (line ("block diffusion hops=" <> show n) [zip samples (fromRational @Double . _ecdf (hopsCDF !! (n - 1)) <$> samples)])
--     plot (line "mainnet (1 mo)" [filter ((<= 5) . fst) mainnet])
--     plot (line "95%" [[(0.0, 0.95), (5.0, 0.95)]])

-- oneHop = do
--   gen <- createSystemRandom
--   certified_block_all_cdf <- empiricalCDF gen 500 (multiHop 4 certBlockAll)
--   plain_block_cdf <- empiricalCDF gen 500 (multiHop 4 oneBlockDiffusion)
--   let samples = fromRational . (% 1000) <$> [0 .. 5000]
--       cert_block_all_data = zip samples (fromRational @Double . _ecdf certified_block_all_cdf <$> samples)
--       plain_block_data = zip samples (fromRational @Double . _ecdf plain_block_cdf <$> samples)

--   toFile def{_fo_format = SVG} "block-with-cert.svg" $ do
--     layout_title .= "4-Hops Block Diffusion w/ Certificate"
--     layout_x_axis . laxis_title .= "time (seconds)"
--     layout_y_axis . laxis_title .= "probability (cumul.)"
--     plot (line "certified block" [cert_block_all_data])
--     plot (line "plain block" [plain_block_data])
--     plot (line "95%" [[(0.0, 0.95), (5.0, 0.95)]])
