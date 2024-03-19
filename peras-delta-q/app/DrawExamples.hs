module DrawExamples where

import A
import NumericalCDF as N

import Graphics.Rendering.Chart.Backend.Cairo (toFile)
import Graphics.Rendering.Chart.Easy (def, layout_title, line, plot, (.=))
import qualified Peras

introGraph :: IO ()
introGraph = do
  let parts = (2000 :: Int)
  let dx = (2.0 / fromIntegral parts :: Double)

  -- NOTE we can put any of our examples here, given that
  --      the parts (and dx) are acceptable.
  let ex = (toCDF Peras.praosHeader :: Double -> NCDF) dx
  let fg = A.tabulate ex dx

  toFile def "do-intro.png" $ do
    layout_title .= "Intro Example"
    plot (line "conv f g" [fg])

perasGraph :: IO ()
perasGraph = do
  let parts = (2000 :: Int)
  let dx = (2.0 / fromIntegral parts :: Double)

  -- NOTE we can put any of our examples here, given that
  --      the parts (and dx) are acceptable.
  let hdr = (toCDF Peras.praosHeader :: Double -> NCDF) dx
      body = (toCDF Peras.praosBody :: Double -> NCDF) dx
      hdrTab = A.tabulate hdr dx
      bodyTab = A.tabulate body dx

  toFile def "do-intro.png" $ do
    layout_title .= "Intro Example"
    plot (line "header" [hdrTab])
    plot (line "body" [bodyTab])

-- TODO this is deprecated code that uses NumericalCDF directly.
--      It should produce exactly the same result as toCDF Examples.doIntro.
--      Remove it.
doIntro :: IO ()
doIntro = do
  let parts = (2000 :: Int)
  let dx = (2.0 / fromIntegral parts :: Double)

  let f = N.uniformN 0 1
  let g = (0.95 *) . N.uniformN 0 1

  let ft = N.tabulate f 2 dx
  let gt = N.tabulate g 2 dx

  -- print ft
  let f' = grad ft dx
  let g' = grad gt dx

  let fg' = N.conv f' g' dx
  let fg = integrate fg' dx

  let ftgt = zipWith (*) (integrate f' dx) (integrate g' dx)

  toFile def "do-intro.png" $ do
    layout_title .= "Intro Example"
    plot (line "conv" [zip (map ((dx *) . fromIntegral) [0 .. (length fg :: Int)]) fg])
    plot (line "ftgt" [zip (map ((dx *) . fromIntegral) [0 .. (length ftgt :: Int)]) ftgt])
