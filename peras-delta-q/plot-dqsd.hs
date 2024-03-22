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

oneMTU =
  fromQTA @SimpleUniform
    [(0, 0), (1 % 3, 0.012), (2 % 3, 0.069), (3 % 3, 0.268)]
blockBody64K =
  fromQTA @SimpleUniform
    [(0, 0), (1 % 3, 0.024), (2 % 3, 0.143), (3 % 3, 0.531)]
headerRequestReply = oneMTU ⊕ oneMTU -- request/reply
bodyRequestReply = oneMTU ⊕ blockBody64K -- request/reply
oneBlockDiffusion = headerRequestReply ⊕ bodyRequestReply

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
  header_exchange_1_hop <- empiricalCDF gen 50 headerRequestReply
  body_exchange_1_hop <- empiricalCDF gen 50 bodyRequestReply
  header_and_body <- empiricalCDF gen 50 oneBlockDiffusion
  let samples = fromRational . (% 100) <$> [0 .. 200]
  writeFile "header.dat" $
    unlines $
      zipWith (curry (\(x, y) -> show x <> "\t" <> show y)) samples (fromRational . _ecdf header_exchange_1_hop <$> samples)
  writeFile "body.dat" $
    unlines $
      zipWith (curry (\(x, y) -> show x <> "\t" <> show y)) samples (fromRational . _ecdf body_exchange_1_hop <$> samples)
  writeFile "header_body.dat" $
    unlines $
      zipWith (curry (\(x, y) -> show x <> "\t" <> show y)) samples (fromRational . _ecdf header_and_body <$> samples)

  let plot =
        [ "set term png size 1200,800"
        , "set output 'plot-praos-1-hop.png'"
        , "plot 'header.dat' w lines t 'header (1 hop)', 'body.dat' w lines t 'body (1 hop)', 'header_body.dat' w lines t 'header+body (1 hop)', 0.95 t '95%'"
        ]

  readProcess "gnuplot" [] (unlines plot)
