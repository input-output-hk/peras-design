{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Haskell.Prim.Bounded where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Haskell.Prim.Int
import qualified MAlonzo.Code.Haskell.Prim.Ord
import qualified MAlonzo.Code.Haskell.Prim.Tuple
import MAlonzo.RTE (
  AgdaAny,
  add64,
  addInt,
  coe,
  eq64,
  eqInt,
  erased,
  geqInt,
  lt64,
  ltInt,
  mul64,
  mulInt,
  quot64,
  quotInt,
  rem64,
  remInt,
  sub64,
  subInt,
  word64FromNat,
  word64ToNat,
 )
import qualified MAlonzo.RTE

-- Haskell.Prim.Bounded.BoundedBelow
d_BoundedBelow_8 a0 = ()
newtype T_BoundedBelow_8 = C_BoundedBelow'46'constructor_3 AgdaAny

-- Haskell.Prim.Bounded.BoundedBelow.minBound
d_minBound_14 :: T_BoundedBelow_8 -> AgdaAny
d_minBound_14 v0 =
  case coe v0 of
    C_BoundedBelow'46'constructor_3 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Bounded.BoundedAbove
d_BoundedAbove_18 a0 = ()
newtype T_BoundedAbove_18
  = C_BoundedAbove'46'constructor_53 AgdaAny

-- Haskell.Prim.Bounded.BoundedAbove.maxBound
d_maxBound_24 :: T_BoundedAbove_18 -> AgdaAny
d_maxBound_24 v0 =
  case coe v0 of
    C_BoundedAbove'46'constructor_53 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Bounded.Bounded
d_Bounded_28 a0 = ()
data T_Bounded_28
  = C_Bounded'46'constructor_111 T_BoundedBelow_8 T_BoundedAbove_18

-- Haskell.Prim.Bounded.Bounded.below
d_below_36 :: T_Bounded_28 -> T_BoundedBelow_8
d_below_36 v0 =
  case coe v0 of
    C_Bounded'46'constructor_111 v1 v2 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Bounded.Bounded.above
d_above_38 :: T_Bounded_28 -> T_BoundedAbove_18
d_above_38 v0 =
  case coe v0 of
    C_Bounded'46'constructor_111 v1 v2 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Bounded._.minBound
d_minBound_42 :: T_BoundedBelow_8 -> AgdaAny
d_minBound_42 v0 = coe d_minBound_14 (coe v0)

-- Haskell.Prim.Bounded._.maxBound
d_maxBound_46 :: T_BoundedAbove_18 -> AgdaAny
d_maxBound_46 v0 = coe d_maxBound_24 (coe v0)

-- Haskell.Prim.Bounded.iBounded
d_iBounded_48 ::
  () -> T_BoundedBelow_8 -> T_BoundedAbove_18 -> T_Bounded_28
d_iBounded_48 ~v0 v1 v2 = du_iBounded_48 v1 v2
du_iBounded_48 ::
  T_BoundedBelow_8 -> T_BoundedAbove_18 -> T_Bounded_28
du_iBounded_48 v0 v1 =
  coe C_Bounded'46'constructor_111 (coe v0) (coe v1)

-- Haskell.Prim.Bounded.iBoundedBelowNat
d_iBoundedBelowNat_50 :: T_BoundedBelow_8
d_iBoundedBelowNat_50 =
  coe C_BoundedBelow'46'constructor_3 (coe (0 :: Integer))

-- Haskell.Prim.Bounded.iBoundedBelowWord
d_iBoundedBelowWord_52 :: T_BoundedBelow_8
d_iBoundedBelowWord_52 =
  coe
    C_BoundedBelow'46'constructor_3
    (coe (0 :: MAlonzo.RTE.Word64))

-- Haskell.Prim.Bounded.iBoundedAboveWord
d_iBoundedAboveWord_54 :: T_BoundedAbove_18
d_iBoundedAboveWord_54 =
  coe
    C_BoundedAbove'46'constructor_53
    (coe (18446744073709551615 :: MAlonzo.RTE.Word64))

-- Haskell.Prim.Bounded.iBoundedBelowInt
d_iBoundedBelowInt_56 :: T_BoundedBelow_8
d_iBoundedBelowInt_56 =
  coe
    C_BoundedBelow'46'constructor_3
    ( coe
        MAlonzo.Code.Haskell.Prim.Int.C_int64_8
        ( coe
            word64FromNat
            ( coe
                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                MAlonzo.Code.Haskell.Prim.Int.d_2'8310''8308'_18
                (9223372036854775808 :: Integer)
            )
        )
    )

-- Haskell.Prim.Bounded.iBoundedAboveInt
d_iBoundedAboveInt_58 :: T_BoundedAbove_18
d_iBoundedAboveInt_58 =
  coe
    C_BoundedAbove'46'constructor_53
    ( coe
        MAlonzo.Code.Haskell.Prim.Int.C_int64_8
        (coe (9223372036854775807 :: MAlonzo.RTE.Word64))
    )

-- Haskell.Prim.Bounded.iBoundedBelowBool
d_iBoundedBelowBool_60 :: T_BoundedBelow_8
d_iBoundedBelowBool_60 =
  coe
    C_BoundedBelow'46'constructor_3
    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)

-- Haskell.Prim.Bounded.iBoundedAboveBool
d_iBoundedAboveBool_62 :: T_BoundedAbove_18
d_iBoundedAboveBool_62 =
  coe
    C_BoundedAbove'46'constructor_53
    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)

-- Haskell.Prim.Bounded.iBoundedBelowChar
d_iBoundedBelowChar_64 :: T_BoundedBelow_8
d_iBoundedBelowChar_64 =
  coe C_BoundedBelow'46'constructor_3 (coe '\NUL')

-- Haskell.Prim.Bounded.iBoundedAboveChar
d_iBoundedAboveChar_66 :: T_BoundedAbove_18
d_iBoundedAboveChar_66 =
  coe C_BoundedAbove'46'constructor_53 (coe '\1114111')

-- Haskell.Prim.Bounded.iBoundedBelowUnit
d_iBoundedBelowUnit_68 :: T_BoundedBelow_8
d_iBoundedBelowUnit_68 =
  coe
    C_BoundedBelow'46'constructor_3
    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)

-- Haskell.Prim.Bounded.iBoundedAboveUnit
d_iBoundedAboveUnit_70 :: T_BoundedAbove_18
d_iBoundedAboveUnit_70 =
  coe
    C_BoundedAbove'46'constructor_53
    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)

-- Haskell.Prim.Bounded.iBoundedBelowTuple₂
d_iBoundedBelowTuple'8322'_72 ::
  () ->
  () ->
  T_BoundedBelow_8 ->
  T_BoundedBelow_8 ->
  T_BoundedBelow_8
d_iBoundedBelowTuple'8322'_72 ~v0 ~v1 v2 v3 =
  du_iBoundedBelowTuple'8322'_72 v2 v3
du_iBoundedBelowTuple'8322'_72 ::
  T_BoundedBelow_8 -> T_BoundedBelow_8 -> T_BoundedBelow_8
du_iBoundedBelowTuple'8322'_72 v0 v1 =
  coe
    C_BoundedBelow'46'constructor_3
    ( coe
        MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24
        (coe d_minBound_14 (coe v0))
        (coe d_minBound_14 (coe v1))
    )

-- Haskell.Prim.Bounded.iBoundedAboveTuple₂
d_iBoundedAboveTuple'8322'_74 ::
  () ->
  () ->
  T_BoundedAbove_18 ->
  T_BoundedAbove_18 ->
  T_BoundedAbove_18
d_iBoundedAboveTuple'8322'_74 ~v0 ~v1 v2 v3 =
  du_iBoundedAboveTuple'8322'_74 v2 v3
du_iBoundedAboveTuple'8322'_74 ::
  T_BoundedAbove_18 -> T_BoundedAbove_18 -> T_BoundedAbove_18
du_iBoundedAboveTuple'8322'_74 v0 v1 =
  coe
    C_BoundedAbove'46'constructor_53
    ( coe
        MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24
        (coe d_maxBound_24 (coe v0))
        (coe d_maxBound_24 (coe v1))
    )

-- Haskell.Prim.Bounded.iBoundedBelowTuple₃
d_iBoundedBelowTuple'8323'_76 ::
  () ->
  () ->
  () ->
  T_BoundedBelow_8 ->
  T_BoundedBelow_8 ->
  T_BoundedBelow_8 ->
  T_BoundedBelow_8
d_iBoundedBelowTuple'8323'_76 ~v0 ~v1 ~v2 v3 v4 v5 =
  du_iBoundedBelowTuple'8323'_76 v3 v4 v5
du_iBoundedBelowTuple'8323'_76 ::
  T_BoundedBelow_8 ->
  T_BoundedBelow_8 ->
  T_BoundedBelow_8 ->
  T_BoundedBelow_8
du_iBoundedBelowTuple'8323'_76 v0 v1 v2 =
  coe
    C_BoundedBelow'46'constructor_3
    ( coe
        MAlonzo.Code.Haskell.Prim.Tuple.C__'44'_'44'__40
        (coe d_minBound_14 (coe v0))
        (coe d_minBound_14 (coe v1))
        (coe d_minBound_14 (coe v2))
    )

-- Haskell.Prim.Bounded.iBoundedAboveTuple₃
d_iBoundedAboveTuple'8323'_78 ::
  () ->
  () ->
  () ->
  T_BoundedAbove_18 ->
  T_BoundedAbove_18 ->
  T_BoundedAbove_18 ->
  T_BoundedAbove_18
d_iBoundedAboveTuple'8323'_78 ~v0 ~v1 ~v2 v3 v4 v5 =
  du_iBoundedAboveTuple'8323'_78 v3 v4 v5
du_iBoundedAboveTuple'8323'_78 ::
  T_BoundedAbove_18 ->
  T_BoundedAbove_18 ->
  T_BoundedAbove_18 ->
  T_BoundedAbove_18
du_iBoundedAboveTuple'8323'_78 v0 v1 v2 =
  coe
    C_BoundedAbove'46'constructor_53
    ( coe
        MAlonzo.Code.Haskell.Prim.Tuple.C__'44'_'44'__40
        (coe d_maxBound_24 (coe v0))
        (coe d_maxBound_24 (coe v1))
        (coe d_maxBound_24 (coe v2))
    )

-- Haskell.Prim.Bounded.iBoundedBelowOrdering
d_iBoundedBelowOrdering_80 :: T_BoundedBelow_8
d_iBoundedBelowOrdering_80 =
  coe
    C_BoundedBelow'46'constructor_3
    (coe MAlonzo.Code.Haskell.Prim.Ord.C_LT_8)

-- Haskell.Prim.Bounded.iBoundedAboveOrdering
d_iBoundedAboveOrdering_82 :: T_BoundedAbove_18
d_iBoundedAboveOrdering_82 =
  coe
    C_BoundedAbove'46'constructor_53
    (coe MAlonzo.Code.Haskell.Prim.Ord.C_GT_12)
