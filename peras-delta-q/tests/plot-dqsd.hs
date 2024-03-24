import Data.Ratio
import DeltaQ.Algebra.DelayModel.SimpleUniform
import DeltaQ.Numeric.CDF
import DeltaQ.QTA.Support
import System.Random.MWC

main = do
    let u1 = fromQTA @SimpleUniform [(0, 0), (1 % 3, 0.012), (2 % 3, 0.069), (3 % 3, 0.268)]
    let u2 = fromQTA @SimpleUniform [(0, 0), (1 % 3, 0.024), (2 % 3, 0.143), (3 % 3, 0.531)]
    let u3 = u1 ⊕ u1 -- request/reply
    gen <- createSystemRandom
    header_exchange_1_hop <- empiricalCDF gen 50 u3
    let u4 = u1 ⊕ u2 -- request/reply
    body_exchange_1_hop <- empiricalCDF gen 50 u4
    header_and_body <- empiricalCDF gen 50 (u3 ⊕ u4)

    let samples = (fromRational . (% 100)) <$> [0 .. 200]
    writeFile "header.dat" $
        unlines $
            map (\(x, y) -> show x <> "\t" <> show y) $
                zip samples (fromRational . _ecdf header_exchange_1_hope <$> samples)
    writeFile "body.dat" $
        unlines $
            map (\(x, y) -> show x <> "\t" <> show y) $
                zip samples (fromRational . _ecdf body_exchange_1_hope <$> samples)
    writeFile "header_body.dat" $
        unlines $
            map (\(x, y) -> show x <> "\t" <> show y) $
                zip samples (fromRational . _ecdf header_and_body <$> samples)

    let plot =
            [ "set term svg size 1200,800"
            , "set output 'plot-peras.svg'"
            , "plot 'header.dat' w lines t 'header', 'body.dat' w lines t 'body', 'header_body.dat' w lines t 'header+body', 0.95 t '95%'"
            ]

    readProcess "gnuplot" [] (unlines plot)
