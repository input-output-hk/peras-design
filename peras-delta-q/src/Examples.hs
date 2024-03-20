module Examples where

import A
import Reals
import UnitInterval

-- Examples
doIntro :: (Rops r, Iops i) => A r i
doIntro =
    let
        f = Uniform (Reals.fromDouble 0) (Reals.fromDouble 1)
        g = ScaleDown (UnitInterval.fromDouble 0.95) f
        fg = f `Conv` g
     in
        fg

-- This implements the following function `f`:
-- f = 0      if x < 3
--     0.5    if x < 5
--     0.95   if x < 6
--     0.9995 otherwise
-- using the base operations of A
simpleQta :: (Rops r, Iops i) => A r i
simpleQta = part03
  where
    toI = UnitInterval.fromDouble
    toR = Reals.fromDouble
    part3 = K (toI (0.9995 Prelude.- 0.95)) (toR 1.0)
    shiftedPart3 = ShiftRight (toR 1.0) part3
    part2 = K (toI (0.95 Prelude.- 0.5)) (toR 1.0)
    part23 = part2 `Plus` shiftedPart3
    shiftedPart23 = ShiftRight (toR 2.0) part23
    part1 = K (toI 0.5) (toR 2.0)
    part13 = part1 `Plus` shiftedPart23
    part03 = ShiftRight (toR 3.0) part13

doSimple :: (Rops r, Iops i) => A r i
doSimple = m
  where
    toI = UnitInterval.fromDouble
    toR = Reals.fromDouble

    f =
        ScaleDown
            (toI 0.999)
            (Uniform (toR 4.0) (toR 6.0))

    -- model :: (Rops r, Iops i) => i -> A r i -> A r i -> A r i
    model r hit miss =
        let
            hitmiss = ScaleDown r hit `Plus` ScaleDown (inv r) miss
            hitmissShift = ShiftRight (toR 0.1) hitmiss
            res = ScaleDown (toI 0.99999) hitmissShift
         in
            res

    m =
        model
            (toI 0.2)
            (Uniform (toR 1.0) (toR 2.0))
            (model (toI 0.9) (Uniform (toR 1.5) (toR 4.0)) f)
