module A where

import Data.List (intercalate)
import Reals
import UnitInterval

-- Interface to CDFs, where t r i is the internal representation
-- of the function from Reals (r) to the Unit Interval (i).
class CDF t where
  type R t
  type I t

  -- Representation of CDF has to carry its max x value
  maxx :: t -> R t

  -- We may have fixed dx for this representation that
  -- all the functions will have to resepect.
  -- dx :: t -> Maybe (R t)

  -- Discretise CDF representation with dx step.
  tabulate :: t -> R t -> [(R t, I t)]

  -- Operations that t has to support
  plus, mult, union :: t -> t -> t

  -- `conv f g dx` is a convolution of PDFs of two given CDFs.
  -- The result of the operation is something like:
  --    integrate (convolution f' g') dx
  conv :: t -> t -> (R t -> t)

  -- Constant function `k v max` defines a CDF that
  -- has constant value (v) on the interval [0 .. max]
  k :: I t -> R t -> t

  -- Uniform distribution `uniform l u` on the
  -- interval [l .. u].
  uniform :: R t -> R t -> t

  -- `scaledown x f` computes `(* x) . f`
  scaledown :: I t -> t -> t

  -- `shiftright x f` computes `f . (- x)` defaulting
  -- to 0 for the values where f is not defined.
  shiftright :: R t -> t -> t

-- Initial model of the CDF (kind of)
data A r i where
  -- Constant function
  K :: i -> r -> A r i
  -- Uniform distribution
  Uniform :: r -> r -> A r i
  -- Scale down the CDF
  ScaleDown :: i -> A r i -> A r i
  -- Shift right by x (convolution with (δ x))
  ShiftRight :: r -> A r i -> A r i
  -- Convolution on PDFs
  Conv :: A r i -> A r i -> A r i
  -- Total pointwise operations _*_ and _\/_ on i points
  Mult, Union :: A r i -> A r i -> A r i
  -- Partial pointwise function on i points with the
  -- constraint (f + g | maxv f < inv (maxv g)).  As
  -- CDFs are monotonically non-decreasing functions,
  -- we only have to check that the sum of maximum values
  -- of both functions are less than 1:
  -- maxv f + maxv g <= 1 =
  -- maxv f <= 1 - maxv g =
  -- maxv f <= inv (maxv g)
  Plus :: A r i -> A r i -> A r i

comp :: (Rops r, Iops i) => A r i -> String
comp = \case
  (K x m) -> mkCall "const" [showI x, showR m]
  (Uniform l u) -> mkCall "uniform" [showR l, showR u]
  (ScaleDown r f) -> mkCall "scaledown" [showI r, comp f]
  (ShiftRight r f) -> mkCall "shiftright" [showR r, comp f]
  -- We hardcode the name of the third argument to `dx` for now.
  (Conv f g) -> mkCall "shiftright" [comp f, comp g, "dx"]
  (Plus f g) -> mkCall "plus" [comp f, comp g]
  (Mult f g) -> mkCall "mult" [comp f, comp g]
  (Union f g) -> mkCall "union" [comp f, comp g]
 where
  showR :: Rops r => r -> String
  showR = show . Reals.toDouble

  showI :: Iops r => r -> String
  showI = show . UnitInterval.toDouble

  mkCall :: String -> [String] -> String
  mkCall f args = concat [f, "(", intercalate ", " args, ")"]

-- A is an initial model of CDF
toCDF :: CDF t => A (R t) (I t) -> (R t -> t)
toCDF (K x m) _ = k x m
toCDF (Uniform l u) _ = uniform l u
toCDF (ScaleDown i f) dx = scaledown i (toCDF f dx)
toCDF (ShiftRight r f) dx = shiftright r (toCDF f dx)
toCDF (Conv f g) dx = (toCDF f dx `conv` toCDF g dx) dx
toCDF (Plus f g) dx = toCDF f dx `plus` toCDF g dx
toCDF (Mult f g) dx = toCDF f dx `mult` toCDF g dx
toCDF (Union f g) dx = toCDF f dx `union` toCDF g dx
