module NumericalCDF where

import qualified A
import Control.Exception (assert)
import UnitInterval ((\/))

-- `grad f dx` computes a numerical derivative of discretised f
-- using second-order scheme:
--   r[0]   = (-3f[0] + 4f[1] - f[2])      / 2dx
--   r[i]   = (f[i+1] - f[i-1])            / 2dx | 1 <= i < n-1
--   r[n-1] = (f[n-3] - 4f[n-2] + 3f[n-1]) / 2dx
--
-- Here is some link from the internet to verify that the
-- coefficients are OK:
-- https://lcn.people.uic.edu/classes/che205s17/docs/che205s17_reading_01e.pdf
-- One can apply more precise shemes.  For example, here is a calculator
-- for the coeffiecients online:
-- https://web.media.mit.edu/~crtaylor/calculator.html
grad :: [Double] -> Double -> [Double]
grad (f0 : f1 : f2 : ys) dx = first : go (f0, f1, f2) ys
 where
  -- First element
  first = (-3 * f0 + 4 * f1 - f2) / (2 * dx)

  -- Middle formula
  mid y0 y2 = (y2 - y0) / (2 * dx)

  -- Function that slides the 3-element window
  -- over the array, specialising the last case:
  go (y0, y1, y2) [] = mid y0 y2 : [(y0 - 4 * y1 + 3 * y2) / (2 * dx)]
  -- Middle elements are computed as:
  go (y0, y1, y2) (y3 : r) = mid y0 y2 : go (y1, y2, y3) r
grad _ _ = error "grad needs at least 3 points to compute the derivative"

-- Convolution for the functions on the domain [0, inf)
-- `conv f g dx` is computed as:
--  conv abcdef ghj _ => align arguments as follows:
--    00abcdef, 0abcdef, abcdef, ..., def, ef,  f
--    jhg       jhg      jhg          jhg  jhg  jhg
--  then for each pair compute dot-product
--  NOTE: this implementation is ridiculously inefficient
--        for any serious size, you want to wrap efficient
--        implementation such one that is based on fftw.
conv :: [Double] -> [Double] -> Double -> [Double]
conv f g dx = reverse $ go fp gr []
 where
  -- Pad f by the lenght of g minus one
  fp = replicate (length g - 1) 0 ++ f
  -- Reverse g
  gr = reverse g

  go [] _ acc = acc
  go as bs acc = go (tail as) bs (dx * sum (zipWith (*) as bs) : acc)

-- Integrate, just a trapezoid rule.
integrate :: [Double] -> Double -> [Double]
integrate [] _ = []
integrate (y : ys) dx = 0 : map (dx *) (go ys y 0)
 where
  go [] _ _ = []
  go (x : xs) p s = let t = s + (p + x) / 2 in t : go xs x t

uniformN :: Double -> Double -> (Double -> Double)
uniformN l u = assert (l < u) $ \x ->
  if x < l
    then 0
    else
      if x < u
        then (x - l) / (u - l)
        else 1

-- `xvalues n dx` generates n consequetive values at the distance dx.
xvalues :: Int -> Double -> [Double]
xvalues n dx = map ((dx *) . fromIntegral) [0 .. n - 1]

tabulate :: (Double -> Double) -> Double -> Double -> [Double]
tabulate f m dx = map f $ xvalues (floor (m / dx)) dx

-- Some trivial tests
-- FIXME: turn them into more sensible tests
gradTest :: [Double]
gradTest = grad [1, 4, 9, 16, 25] 1

convTest :: [Double]
convTest = NumericalCDF.conv [1, 2, 3, 4, 5, 6] [1, 2, 3, 4, 5, 6] 1

integrateTest :: [Double]
integrateTest = integrate [1, 2, 3] 1

-- Numerical CDF that tries to keep pure functions
-- as long as possible.
data NCDF where
  -- `Fun maxx f` is a CDF where maxx is the boundary
  -- at which f becomes a constant function.
  Fun :: Double -> (Double -> Double) -> NCDF
  -- `Tab dx ys` is a tabulated function that always
  -- starts at zero with a step fixed to dx.
  Tab :: Double -> [Double] -> NCDF

-- Extend the tabulated function by replicating last element
extend :: [Double] -> Int -> [Double]
extend ys l =
  assert (l >= length ys && not (null ys)) $
    ys ++ replicate (l - length ys) (last ys)

-- liftBinaryOpTab :: (Double -> Double -> Double) -> [Double] -> [Double] -> [Double]
-- liftBinaryOpTab f xs ys = zipWith f xs' ys'
--   where
--     m = max (length xs) (length ys)
--     xs' = extend xs m
--     ys' = extend ys m
--
-- liftBinaryOpFun :: (Double -> Double -> Double)
--                 -> (Double -> Double) -> (Double -> Double)
--                 -> (Double -> Double)
-- liftBinaryOpFun op f g x = f x `op` g x

liftBinaryOp ::
  (Double -> Double -> Double) ->
  NCDF ->
  NCDF ->
  NCDF
liftBinaryOp op (Fun m f) (Fun m' g) =
  Fun (max m m') (\x -> f x `op` g x)
liftBinaryOp op (Fun m f) (Tab dx gv) =
  liftBinaryOp op (Tab dx (tabulate f m dx)) (Tab dx gv)
liftBinaryOp op (Tab dx fv) (Fun m g) =
  liftBinaryOp op (Tab dx fv) (Tab dx (tabulate g m dx))
liftBinaryOp op (Tab dx fv) (Tab dx' gv) =
  assert (dx == dx') $ Tab dx $ zipWith op fv' gv'
 where
  m = max (length fv) (length gv)
  fv' = extend fv m
  gv' = extend gv m

convN :: NCDF -> NCDF -> Double -> NCDF
convN (Tab dx1 fv) (Tab dx2 gv) dx =
  assert (dx1 == dx && dx2 == dx) $
    Tab dx $
      integrate (conv (grad fv dx) (grad gv dx) dx) dx
convN f@(Tab dx1 _) (Fun m g) dx =
  assert (dx1 == dx) $
    convN f (Tab dx $ tabulate g m dx) dx
convN (Fun m f) g@(Tab dx2 _) dx =
  assert (dx2 == dx) $
    convN (Tab dx $ tabulate f m dx) g dx
convN (Fun m1 f) (Fun m2 g) dx =
  convN (Tab dx $ tabulate f m1 dx) (Tab dx $ tabulate g m2 dx) dx

instance A.CDF NCDF where
  type R NCDF = Double
  type I NCDF = Double

  maxx (Fun m _) = m
  maxx (Tab _ []) = 0
  maxx (Tab dx ys) = dx * fromIntegral (length ys - 1)

  tabulate (Fun m f) dx =
    let fv = tabulate f m dx
     in zip (xvalues (length fv) dx) fv
  tabulate (Tab dx ys) dx' =
    assert (dx == dx') $
      zip (xvalues (length ys) dx) ys

  k v m = Fun m (const v)

  -- XXX: here we give an extra tail to the uniform distribution
  --      so that it looks nicer on the graphs
  uniform l u = Fun (1 + u) (uniformN l u)

  plus = liftBinaryOp (+)
  mult = liftBinaryOp (*)
  union = liftBinaryOp (\/)

  scaledown i (Fun m f) = Fun m ((* i) . f)
  scaledown i (Tab dx fv) = Tab dx (map (* i) fv)

  shiftright r (Fun m f) = Fun (r + m) (\x -> if x < r then 0 else f (x - r))
  shiftright r (Tab dx fv) = Tab dx (replicate (floor (r / dx)) 0 ++ fv)

  conv = convN
