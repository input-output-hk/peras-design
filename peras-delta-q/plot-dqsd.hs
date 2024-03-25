{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Control.Exception (IOException, try)
import Control.Monad (forM, forM_)
import Data.Bifunctor (bimap)
import Data.Ratio
import Data.Traversable (for)
import DeltaQ.Algebra.Class
import DeltaQ.Algebra.DelayModel.SimpleUniform
import DeltaQ.Algebra.Simplification (normaliseDeltaQ)
import DeltaQ.Numeric.CDF
import DeltaQ.QTA.Support
import Graphics.Rendering.Chart.Backend.Cairo (FileFormat (SVG), FileOptions (_fo_format), toFile)
import Graphics.Rendering.Chart.Easy (def, layout_title, line, plot, (.=))
import System.IO (IOMode (ReadMode), hGetLine, withFile)
import System.Process
import System.Random.MWC

main = do
  oneHop
  hopsDistribution 5
  hopsProbability
  networkWithCertsProbability

oneMTU =
  fromQTA @SimpleUniform
    [(0, 0), (1 % 3, 0.012), (2 % 3, 0.069), (3 % 3, 0.268)]
blockBody64K =
  fromQTA @SimpleUniform
    [(0, 0), (1 % 3, 0.024), (2 % 3, 0.143), (3 % 3, 0.531)]
headerRequestReply = oneMTU ⊕ oneMTU -- request/reply
bodyRequestReply = oneMTU ⊕ blockBody64K -- request/reply
oneBlockDiffusion = headerRequestReply ⊕ bodyRequestReply

certRequestReply = oneMTU ⊕ oneMTU -- request/reply
certValidation = uniform0 @SimpleUniform (0.050 :: Double)
certHandling = certRequestReply ⊕ certValidation
headerWithCert = (⇋) (1 % 3) (headerRequestReply ⊕ certHandling) headerRequestReply
certBlockOneThird = headerWithCert ⊕ bodyRequestReply
certBlockAll = headerRequestReply ⊕ certHandling ⊕ bodyRequestReply

combine [(p, dq), (_, dq')] = (⇋) (toRational $ p / 100) dq dq'
combine ((p, dq) : rest) = (⇋) (toRational $ p / 100) dq (combine rest)

multihops = (`multiHop` oneBlockDiffusion) <$> [1 ..]

-- model for average degree 15
pathLengthsDistributionDegree15 =
  [0.60, 8.58, 65.86, 24.95]
hopsProba15 = zip (scanl1 (+) pathLengthsDistributionDegree15 <> [0]) multihops
deltaq15 = combine hopsProba15

-- model for average degree 10
pathLengthsDistributionDegree10 =
  [0.40, 3.91, 31.06, 61.85, 2.78]
hopsProba10 = zip (scanl1 (+) pathLengthsDistributionDegree10 <> [0]) multihops
deltaq10 = combine hopsProba10

certAllDeltaQ15 =
  combine $ zip (scanl1 (+) pathLengthsDistributionDegree10 <> [0]) $ (`multiHop` certBlockAll) <$> [1 ..]
certOneThirdDeltaQ15 =
  combine $ zip (scanl1 (+) pathLengthsDistributionDegree10 <> [0]) $ (`multiHop` certBlockOneThird) <$> [1 ..]

networkWithCertsProbability = do
  gen <- createSystemRandom
  cdf15 <- empiricalCDF gen 500 deltaq15
  certAllCdf <- empiricalCDF gen 500 certAllDeltaQ15
  certOneThirdCdf <- empiricalCDF gen 500 certOneThirdDeltaQ15
  let samples = fromRational . (% 1000) <$> [0 .. 6000]
      cdf15Data = zip samples (fromRational @Double . _ecdf cdf15 <$> samples)
      certAllData = zip samples (fromRational @Double . _ecdf certAllCdf <$> samples)
      certOneThirdData = zip samples (fromRational @Double . _ecdf certOneThirdCdf <$> samples)

  toFile def{_fo_format = SVG} "network-with-cert.svg" $ do
    layout_title .= "Peras Network Diffusion (δ=15)"
    plot (line "block diffusion w/o cert" [cdf15Data])
    plot (line "block diffusion w/o 1/3 cert" [certOneThirdData])
    plot (line "block diffusion w/o 100% cert" [certAllData])
    plot (line "95%" [[(0.0, 0.95), (6.0, 0.95)]])

hopsProbability = do
  gen <- createSystemRandom
  cdf15 <- empiricalCDF gen 500 deltaq15
  cdf10 <- empiricalCDF gen 500 deltaq10
  let samples = fromRational . (% 1000) <$> [0 .. 5000]
      cdf15Data = zip samples (fromRational @Double . _ecdf cdf15 <$> samples)
      cdf10Data = zip samples (fromRational @Double . _ecdf cdf10 <$> samples)

  toFile def{_fo_format = SVG} "peras.svg" $ do
    layout_title .= "Praos Network Diffusion"
    plot (line "block diffusion (δ=15)" [cdf15Data])
    plot (line "block diffusion (δ=10)" [cdf10Data])
    plot (line "95%" [[(0.0, 0.95), (5.0, 0.95)]])

hopsDistribution n = do
  let hops = [1 .. n]
  gen <- createSystemRandom
  hopsCDF <- forM hops $ \n -> empiricalCDF gen 500 (n `multiHop` oneBlockDiffusion)
  let samples = fromRational . (% 1000) <$> [0 .. 5000]

      loop acc h =
        try (hGetLine h) >>= \case
          Left (_ :: IOException) -> pure $ reverse acc
          Right line ->
            let l = bimap ((/ 100) . read) read $ break (== '\t') line
             in loop (l : acc) h

  mainnet :: [(Double, Double)] <- withFile "block-diffusion" ReadMode $ loop []

  toFile def{_fo_format = SVG} "praos-multi-hops.svg" $ do
    layout_title .= "Praos Multi-Hops Block diffusion"
    forM_ hops $ \n ->
      plot (line ("block diffusion hops=" <> show n) [zip samples (fromRational @Double . _ecdf (hopsCDF !! (n - 1)) <$> samples)])
    plot (line "mainnet (1 mo)" [filter ((<= 5) . fst) mainnet])
    plot (line "95%" [[(0.0, 0.95), (5.0, 0.95)]])

multiHop n dq =
  iterate (dq ⊕) dq !! max 0 (n - 1)

oneHop = do
  gen <- createSystemRandom
  certified_block_cdf <- empiricalCDF gen 500 (multiHop 4 certBlockOneThird)
  certified_block_all_cdf <- empiricalCDF gen 500 (multiHop 4 certBlockAll)
  plain_block_cdf <- empiricalCDF gen 500 (multiHop 4 oneBlockDiffusion)
  let samples = fromRational . (% 1000) <$> [0 .. 5000]
      cert_block_data = zip samples (fromRational @Double . _ecdf certified_block_cdf <$> samples)
      cert_block_all_data = zip samples (fromRational @Double . _ecdf certified_block_all_cdf <$> samples)
      plain_block_data = zip samples (fromRational @Double . _ecdf plain_block_cdf <$> samples)

  toFile def{_fo_format = SVG} "block-with-cert.svg" $ do
    layout_title .= "4-Hops Block Diffusion w/ Certificate"
    plot (line "1/3 certified block" [cert_block_data])
    plot (line "All certified block" [cert_block_all_data])
    plot (line "plain block" [plain_block_data])
    plot (line "95%" [[(0.0, 0.95), (5.0, 0.95)]])
