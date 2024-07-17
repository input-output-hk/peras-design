{-# LANGUAGE ScopedTypeVariables #-}

import Data.Ratio
import DeltaQ.Algebra (perfection)
import DeltaQ.Algebra.Class
import DeltaQ.Algebra.DelayModel.SimpleUniform
import DeltaQ.Numeric.CDF
import DeltaQ.QTA.Support
import Graphics.Rendering.Chart.Backend.Cairo (FileFormat (SVG), FileOptions (_fo_format), toFile)
import Graphics.Rendering.Chart.Easy (def, layout_title, line, plot, (.=))
import System.Random.MWC

-- Voting process
--  1. a voter emits a vote -> takes some time ?
--  2. vote is pulled by peers -> 1 hop 1 MTU transmission
--  3. vote is validate -> takes some time ?
--  4. go to 2

-- model assumes there's no congestion, e.g reception of individual votes do not interfere with one anothers
-- is this really true?

-- Goal:
-- - votes are coming from the network
-- - could start from some expected distance distribution of votes count
main :: IO ()
main = hopsProbability

multihops :: [DeltaQ (Ratio Integer) SimpleUniform Double]
multihops = (`multiHop` oneMTU) <$> [1 ..]

multiHop :: Int -> DeltaQ p d n -> DeltaQ p d n
multiHop n dq = iterate (dq ⊕) dq !! max 0 (n - 1)

pathLengthsDistributionDegree15 :: [Double]
pathLengthsDistributionDegree15 = [0.60, 8.58, 65.86, 24.95]

oneMTU :: DeltaQ (Ratio Integer) SimpleUniform Double
oneMTU =
  fromQTA @SimpleUniform [(0, 0), (1 % 3, 0.012), (2 % 3, 0.069), (3 % 3, 0.268)]

verificationTime :: DeltaQ Rational SimpleUniform Double
verificationTime =
  fromQTA @SimpleUniform [(0, 0), (1, 0.15)]

combine :: (Real a, Fractional a) => [(a, DeltaQ Rational d n)] -> DeltaQ Rational d n
combine [(p, dq), (_, dq')] = (⇋) (toRational $ p / 100) dq dq'
combine ((p, dq) : rest) = (⇋) (toRational $ p / 100) dq (combine rest)
combine [] = perfection

hopsProba15 :: [(Double, DeltaQ (Ratio Integer) SimpleUniform Double)]
hopsProba15 = zip (scanl1 (+) pathLengthsDistributionDegree15 <> [0]) multihops

deltaq15 :: DeltaQ Rational SimpleUniform Double
deltaq15 = combine hopsProba15 ⊕ verificationTime

serialVerification :: DeltaQ Rational SimpleUniform Double
serialVerification =
  NToFinish 75 (replicate 1000 deltaq15) ⊕ verificationTime

parallelVerification :: DeltaQ Rational SimpleUniform Double
parallelVerification =
  NToFinish 75 (replicate 1000 (deltaq15 ⊕ oneVoteVerificationDelay))

oneVoteVerificationDelay :: DeltaQ Rational SimpleUniform Double
oneVoteVerificationDelay = Delay $ DiracDelta 0.00015

hopsProbability :: IO ()
hopsProbability = do
  gen <- createSystemRandom
  path4 <- empiricalCDF gen 1000 serialVerification
  parallel <- empiricalCDF gen 1000 parallelVerification
  path15 <- empiricalCDF gen 1000 deltaq15
  let samples = fromRational . (% 1000) <$> [0 .. 1500]
      path4data = zip samples (fromRational @Double . _ecdf path4 <$> samples)
      path15data = zip samples (fromRational @Double . _ecdf path15 <$> samples)
      parallelData = zip samples (fromRational @Double . _ecdf parallel <$> samples)

  toFile def{_fo_format = SVG} "vote-diffusion.svg" $ do
    layout_title .= "Peras Vote Diffusion"
    plot (line "worst case 75% vote diffusion" [path4data])
    plot (line "parallel verification 75% vote diffusion" [parallelData])
    plot (line "single vote" [path15data])
    plot (line "75%" [[(0.0, 0.75), (1.5, 0.75)]])
