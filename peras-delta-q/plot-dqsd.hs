import Control.Monad (forM, forM_)
import Data.Ratio
import DeltaQ.Algebra.Class
import DeltaQ.Algebra.DelayModel.SimpleUniform
import DeltaQ.Algebra.Simplification (normaliseDeltaQ)
import DeltaQ.Numeric.CDF
import DeltaQ.QTA.Support
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
    writeFile "hops-combined-15.dat" $
        unlines $
            zipWith (curry (\(x, y) -> show x <> "\t" <> show y)) samples (fromRational . _ecdf cdf15 <$> samples)

    writeFile "hops-combined-10.dat" $
        unlines $
            zipWith (curry (\(x, y) -> show x <> "\t" <> show y)) samples (fromRational . _ecdf cdf10 <$> samples)

    let plot =
            [ "set term svg size 1200,800"
            , "set output 'plot-hops-distribution.svg'"
            , "plot 'hops-combined-15.dat' w lines t 'block diffusion (δ=15)', 'hops-combined-10.dat' w lines t 'block diffusion (δ=10)', 0.95 t '95%'"
            ]

    readProcess "gnuplot" [] (unlines plot)

hopsDistribution n = do
    let hops = [1 .. n]
    gen <- createSystemRandom
    hopsCDF <- forM hops $ \n -> empiricalCDF gen 500 (n `multiHop` oneBlockDiffusion)
    let samples = fromRational . (% 1000) <$> [0 .. 5000]
    forM_ hops $ \n ->
        writeFile ("hop-" <> show n <> ".dat") $
            unlines $
                map (\(x, y) -> show x <> "\t" <> show y) $
                    zip samples (fromRational . _ecdf (hopsCDF !! (n - 1)) <$> samples)
    let hopsPlot i = "'hop-" <> show i <> ".dat' w lines t '" <> show i <> " hop',"
        plot =
            [ "set term svg size 1200,800"
            , "set xrange [0:8]"
            , "set output 'plot-praos-multi-hops.svg'"
            , "plot 'block-diffusion' u ($1*.01):2 w line t 'mainnet (1 mo)', " <> concatMap hopsPlot hops <> " 0.95 t '95%'"
            ]

    readProcess "gnuplot" [] (unlines plot)

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
