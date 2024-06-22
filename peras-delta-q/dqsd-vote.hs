{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

import Control.Exception (IOException, try)
import Control.Monad (forM, forM_)
import Data.Bifunctor (bimap)
import Data.Ratio
import DeltaQ.Algebra.Class
import DeltaQ.Algebra.DelayModel.SimpleUniform
import DeltaQ.Numeric.CDF
import DeltaQ.QTA.Support
import Graphics.Rendering.Chart.Backend.Cairo (FileFormat (SVG), FileOptions (_fo_format), toFile)
import Graphics.Rendering.Chart.Easy (def, laxis_title, layout_title, layout_x_axis, layout_y_axis, line, plot, (.=))
import System.IO (IOMode (ReadMode), hGetLine, withFile)
import System.Random.MWC

-- Voting process
--  1. a voter emits a vote -> takes some time ?
--  2. vote is pulled by peers -> 1 hop 1 MTU transmission
--  3. vote is validate -> takes some time ?
--  4. go to 2

-- seems like timings is dominated by verification and therefore CPU time

-- Goal:
-- - votes are coming from the network
-- - could start from some expected distance distribution of votes count
main = hopsProbability

multihops = (`multiHop` oneMTU) <$> [1 ..]

multiHop n dq = iterate (dq ⊕) dq !! max 0 (n - 1)

pathLengthsDistributionDegree15 :: [Double]
pathLengthsDistributionDegree15 = [0.60, 8.58, 65.86, 24.95]

-- Assuming we need 1.3ms to verify a single vote -> * 1000 votes = 1.3s max
-- So distributing uniformly the verification time for the 1000 votes in 10% buckets to reach
-- a mean of 0.65s
verificationTime =
  fromQTA @SimpleUniform ((0, 0) : [(i % 10, fromIntegral i * 1.3 / 10) | i <- [1 .. 10]])

oneMTU =
  fromQTA @SimpleUniform [(0, 0), (1 % 3, 0.012), (2 % 3, 0.069), (3 % 3, 0.268)]

combine [(p, dq), (_, dq')] = (⇋) (toRational $ p / 100) dq dq'
combine ((p, dq) : rest) = (⇋) (toRational $ p / 100) dq (combine rest)

hopsProba15 = zip (scanl1 (+) pathLengthsDistributionDegree15 <> [0]) multihops
deltaq15 = combine hopsProba15 ⊕ verificationTime

hopsProbability = do
  gen <- createSystemRandom
  path4 <- empiricalCDF gen 500 deltaq15
  let samples = fromRational . (% 1000) <$> [0 .. 3000]
      path4data = zip samples (fromRational @Double . _ecdf path4 <$> samples)

  toFile def{_fo_format = SVG} "path.svg" $ do
    layout_title .= "Peras Vote Diffusion"
    plot (line "vote diffusion (δ=15)" [path4data])
    plot (line "quorum (3/4)" [[(0.0, 0.75), (3, 0.75)]])

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

-- blockBody64K =
--   fromQTA @SimpleUniform
--     [(0, 0), (1 % 3, 0.024), (2 % 3, 0.143), (3 % 3, 0.531)]
-- headerRequestReply = oneMTU ⊕ oneMTU -- request/reply
-- bodyRequestReply = oneMTU ⊕ blockBody64K -- request/reply
-- oneBlockDiffusion = headerRequestReply ⊕ bodyRequestReply

-- certRequestReply = oneMTU ⊕ oneMTU -- request/reply
-- certValidation = uniform0 @SimpleUniform (0.050 :: Double)
-- certHandling = certRequestReply ⊕ certValidation
-- headerWithCert = (⇋) (1 % 3) (headerRequestReply ⊕ certHandling) headerRequestReply
-- certBlockOneThird = headerWithCert ⊕ bodyRequestReply
-- certBlockAll = headerRequestReply ⊕ certHandling ⊕ bodyRequestReply

-- -- model for average degree 10
-- pathLengthsDistributionDegree10 =
--   [0.40, 3.91, 31.06, 61.85, 2.78]
-- hopsProba10 = zip (scanl1 (+) pathLengthsDistributionDegree10 <> [0]) multihops
-- deltaq10 = combine hopsProba10

-- certAllDeltaQ15 =
--   combine $ zip (scanl1 (+) pathLengthsDistributionDegree10 <> [0]) $ (`multiHop` certBlockAll) <$> [1 ..]
-- certOneThirdDeltaQ15 =
--   combine $ zip (scanl1 (+) pathLengthsDistributionDegree10 <> [0]) $ (`multiHop` certBlockOneThird) <$> [1 ..]

-- networkWithCertsProbability = do
--   gen <- createSystemRandom
--   cdf15 <- empiricalCDF gen 500 deltaq15
--   certAllCdf <- empiricalCDF gen 500 certAllDeltaQ15
--   let samples = fromRational . (% 1000) <$> [0 .. 6000]
--       cdf15Data = zip samples (fromRational @Double . _ecdf cdf15 <$> samples)
--       certAllData = zip samples (fromRational @Double . _ecdf certAllCdf <$> samples)

--   toFile def{_fo_format = SVG} "network-with-cert.svg" $ do
--     layout_title .= "Peras Network Diffusion (δ=15)"
--     layout_x_axis . laxis_title .= "time (seconds)"
--     layout_y_axis . laxis_title .= "probability (cumul.)"
--     plot (line "block diffusion w/o cert" [cdf15Data])
--     plot (line "block diffusion w/ cert" [certAllData])
--     plot (line "95%" [[(0.0, 0.95), (6.0, 0.95)]])
