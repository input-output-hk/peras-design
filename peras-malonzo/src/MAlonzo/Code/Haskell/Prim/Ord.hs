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

module MAlonzo.Code.Haskell.Prim.Ord where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Float
import qualified MAlonzo.Code.Haskell.Prim
import qualified MAlonzo.Code.Haskell.Prim.Bool
import qualified MAlonzo.Code.Haskell.Prim.Either
import qualified MAlonzo.Code.Haskell.Prim.Eq
import qualified MAlonzo.Code.Haskell.Prim.Int
import qualified MAlonzo.Code.Haskell.Prim.Integer
import qualified MAlonzo.Code.Haskell.Prim.Maybe
import qualified MAlonzo.Code.Haskell.Prim.Monoid
import qualified MAlonzo.Code.Haskell.Prim.Tuple
import qualified MAlonzo.Code.Haskell.Prim.Word
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

-- Haskell.Prim.Ord.Ordering
d_Ordering_6 = ()
data T_Ordering_6 = C_LT_8 | C_EQ_10 | C_GT_12

-- Haskell.Prim.Ord.iEqOrdering
d_iEqOrdering_14 :: MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8
d_iEqOrdering_14 =
  coe
    MAlonzo.Code.Haskell.Prim.Eq.C_Eq'46'constructor_7
    ( coe
        ( \v0 ->
            case coe v0 of
              C_LT_8 ->
                coe
                  ( \v1 ->
                      let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                       in coe
                            ( case coe v1 of
                                C_LT_8 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                _ -> coe v2
                            )
                  )
              C_EQ_10 ->
                coe
                  ( \v1 ->
                      let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                       in coe
                            ( case coe v1 of
                                C_EQ_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                _ -> coe v2
                            )
                  )
              C_GT_12 ->
                coe
                  ( \v1 ->
                      let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                       in coe
                            ( case coe v1 of
                                C_GT_12 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                _ -> coe v2
                            )
                  )
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )

-- Haskell.Prim.Ord.iSemigroupOrdering
d_iSemigroupOrdering_16 ::
  MAlonzo.Code.Haskell.Prim.Monoid.T_Semigroup_8
d_iSemigroupOrdering_16 =
  coe
    MAlonzo.Code.Haskell.Prim.Monoid.C_Semigroup'46'constructor_7
    ( coe
        ( \v0 ->
            case coe v0 of
              C_LT_8 -> coe (\v1 -> v0)
              C_EQ_10 -> coe (\v1 -> v1)
              C_GT_12 -> coe (\v1 -> v0)
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )

-- Haskell.Prim.Ord.iMonoidOrdering
d_iMonoidOrdering_20 ::
  MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74
d_iMonoidOrdering_20 =
  coe
    MAlonzo.Code.Haskell.Prim.Monoid.C_Monoid'46'constructor_4387
    (coe C_EQ_10)
    (coe d_iSemigroupOrdering_16)
    ( coe
        MAlonzo.Code.Haskell.Prim.Monoid.du_mappend_108
        ( coe
            MAlonzo.Code.Haskell.Prim.Monoid.C_DefaultMonoid'46'constructor_4503
            (coe C_EQ_10)
            (coe d_iSemigroupOrdering_16)
        )
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.Monoid.du_mconcat_110
        ( coe
            MAlonzo.Code.Haskell.Prim.Monoid.C_DefaultMonoid'46'constructor_4503
            (coe C_EQ_10)
            (coe d_iSemigroupOrdering_16)
        )
    )

-- Haskell.Prim.Ord._.mempty
d_mempty_30 :: T_Ordering_6
d_mempty_30 = coe C_EQ_10

-- Haskell.Prim.Ord._.super
d_super_32 :: MAlonzo.Code.Haskell.Prim.Monoid.T_Semigroup_8
d_super_32 = coe d_iSemigroupOrdering_16

-- Haskell.Prim.Ord.Ord
d_Ord_36 a0 = ()
data T_Ord_36
  = C_Ord'46'constructor_505
      (AgdaAny -> AgdaAny -> T_Ordering_6)
      (AgdaAny -> AgdaAny -> Bool)
      (AgdaAny -> AgdaAny -> Bool)
      (AgdaAny -> AgdaAny -> Bool)
      (AgdaAny -> AgdaAny -> Bool)
      (AgdaAny -> AgdaAny -> AgdaAny)
      (AgdaAny -> AgdaAny -> AgdaAny)
      MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8

-- Haskell.Prim.Ord.Ord.compare
d_compare_56 :: T_Ord_36 -> AgdaAny -> AgdaAny -> T_Ordering_6
d_compare_56 v0 =
  case coe v0 of
    C_Ord'46'constructor_505 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Ord.Ord._<_
d__'60'__58 :: T_Ord_36 -> AgdaAny -> AgdaAny -> Bool
d__'60'__58 v0 =
  case coe v0 of
    C_Ord'46'constructor_505 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Ord.Ord._>_
d__'62'__60 :: T_Ord_36 -> AgdaAny -> AgdaAny -> Bool
d__'62'__60 v0 =
  case coe v0 of
    C_Ord'46'constructor_505 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Ord.Ord._>=_
d__'62''61'__62 :: T_Ord_36 -> AgdaAny -> AgdaAny -> Bool
d__'62''61'__62 v0 =
  case coe v0 of
    C_Ord'46'constructor_505 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v4
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Ord.Ord._<=_
d__'60''61'__64 :: T_Ord_36 -> AgdaAny -> AgdaAny -> Bool
d__'60''61'__64 v0 =
  case coe v0 of
    C_Ord'46'constructor_505 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v5
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Ord.Ord.max
d_max_66 :: T_Ord_36 -> AgdaAny -> AgdaAny -> AgdaAny
d_max_66 v0 =
  case coe v0 of
    C_Ord'46'constructor_505 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v6
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Ord.Ord.min
d_min_68 :: T_Ord_36 -> AgdaAny -> AgdaAny -> AgdaAny
d_min_68 v0 =
  case coe v0 of
    C_Ord'46'constructor_505 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v7
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Ord.Ord.super
d_super_70 :: T_Ord_36 -> MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8
d_super_70 v0 =
  case coe v0 of
    C_Ord'46'constructor_505 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v8
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Ord._._<_
d__'60'__74 :: T_Ord_36 -> AgdaAny -> AgdaAny -> Bool
d__'60'__74 v0 = coe d__'60'__58 (coe v0)

-- Haskell.Prim.Ord._._<=_
d__'60''61'__76 :: T_Ord_36 -> AgdaAny -> AgdaAny -> Bool
d__'60''61'__76 v0 = coe d__'60''61'__64 (coe v0)

-- Haskell.Prim.Ord._._>_
d__'62'__78 :: T_Ord_36 -> AgdaAny -> AgdaAny -> Bool
d__'62'__78 v0 = coe d__'62'__60 (coe v0)

-- Haskell.Prim.Ord._._>=_
d__'62''61'__80 :: T_Ord_36 -> AgdaAny -> AgdaAny -> Bool
d__'62''61'__80 v0 = coe d__'62''61'__62 (coe v0)

-- Haskell.Prim.Ord._.compare
d_compare_82 :: T_Ord_36 -> AgdaAny -> AgdaAny -> T_Ordering_6
d_compare_82 v0 = coe d_compare_56 (coe v0)

-- Haskell.Prim.Ord._.max
d_max_84 :: T_Ord_36 -> AgdaAny -> AgdaAny -> AgdaAny
d_max_84 v0 = coe d_max_66 (coe v0)

-- Haskell.Prim.Ord._.min
d_min_86 :: T_Ord_36 -> AgdaAny -> AgdaAny -> AgdaAny
d_min_86 v0 = coe d_min_68 (coe v0)

-- Haskell.Prim.Ord._.super
d_super_88 :: T_Ord_36 -> MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8
d_super_88 v0 = coe d_super_70 (coe v0)

-- Haskell.Prim.Ord.ordFromCompare
d_ordFromCompare_90 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  (AgdaAny -> AgdaAny -> T_Ordering_6) ->
  T_Ord_36
d_ordFromCompare_90 ~v0 v1 v2 = du_ordFromCompare_90 v1 v2
du_ordFromCompare_90 ::
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  (AgdaAny -> AgdaAny -> T_Ordering_6) ->
  T_Ord_36
du_ordFromCompare_90 v0 v1 =
  coe
    C_Ord'46'constructor_505
    (coe v1)
    ( coe
        ( \v2 v3 ->
            coe
              MAlonzo.Code.Haskell.Prim.Eq.d__'61''61'__14
              d_iEqOrdering_14
              (coe v1 v2 v3)
              (coe C_LT_8)
        )
    )
    ( coe
        ( \v2 v3 ->
            coe
              MAlonzo.Code.Haskell.Prim.Eq.d__'61''61'__14
              d_iEqOrdering_14
              (coe v1 v2 v3)
              (coe C_GT_12)
        )
    )
    ( coe
        ( \v2 v3 ->
            coe
              MAlonzo.Code.Haskell.Prim.Eq.du__'47''61'__16
              (coe d_iEqOrdering_14)
              (coe v1 v2 v3)
              (coe C_LT_8)
        )
    )
    ( coe
        ( \v2 v3 ->
            coe
              MAlonzo.Code.Haskell.Prim.Eq.du__'47''61'__16
              (coe d_iEqOrdering_14)
              (coe v1 v2 v3)
              (coe C_GT_12)
        )
    )
    ( coe
        ( \v2 v3 ->
            coe
              MAlonzo.Code.Haskell.Prim.du_if_then_else__68
              ( coe
                  MAlonzo.Code.Haskell.Prim.Eq.d__'61''61'__14
                  d_iEqOrdering_14
                  (coe v1 v2 v3)
                  (coe C_LT_8)
              )
              (coe (\v4 -> v3))
              (coe (\v4 -> v2))
        )
    )
    ( coe
        ( \v2 v3 ->
            coe
              MAlonzo.Code.Haskell.Prim.du_if_then_else__68
              ( coe
                  MAlonzo.Code.Haskell.Prim.Eq.d__'61''61'__14
                  d_iEqOrdering_14
                  (coe v1 v2 v3)
                  (coe C_GT_12)
              )
              (coe (\v4 -> v3))
              (coe (\v4 -> v2))
        )
    )
    (coe v0)

-- Haskell.Prim.Ord.ordFromLessThan
d_ordFromLessThan_130 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  (AgdaAny -> AgdaAny -> Bool) ->
  T_Ord_36
d_ordFromLessThan_130 ~v0 v1 v2 = du_ordFromLessThan_130 v1 v2
du_ordFromLessThan_130 ::
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  (AgdaAny -> AgdaAny -> Bool) ->
  T_Ord_36
du_ordFromLessThan_130 v0 v1 =
  coe
    C_Ord'46'constructor_505
    ( coe
        ( \v2 v3 ->
            coe
              MAlonzo.Code.Haskell.Prim.du_if_then_else__68
              (coe v1 v2 v3)
              (coe (\v4 -> coe C_LT_8))
              ( coe
                  ( \v4 ->
                      coe
                        MAlonzo.Code.Haskell.Prim.du_if_then_else__68
                        (coe MAlonzo.Code.Haskell.Prim.Eq.d__'61''61'__14 v0 v2 v3)
                        (coe (\v5 -> coe C_EQ_10))
                        (coe (\v5 -> coe C_GT_12))
                  )
              )
        )
    )
    (coe (\v2 v3 -> coe v1 v2 v3))
    (coe (\v2 v3 -> coe v1 v3 v2))
    ( coe
        ( \v2 v3 ->
            MAlonzo.Code.Haskell.Prim.Bool.d__'124''124'__10
              (coe v1 v3 v2)
              (coe MAlonzo.Code.Haskell.Prim.Eq.d__'61''61'__14 v0 v2 v3)
        )
    )
    ( coe
        ( \v2 v3 ->
            MAlonzo.Code.Haskell.Prim.Bool.d__'124''124'__10
              (coe v1 v2 v3)
              (coe MAlonzo.Code.Haskell.Prim.Eq.d__'61''61'__14 v0 v2 v3)
        )
    )
    ( coe
        ( \v2 v3 ->
            coe
              MAlonzo.Code.Haskell.Prim.du_if_then_else__68
              (coe v1 v2 v3)
              (coe (\v4 -> v3))
              (coe (\v4 -> v2))
        )
    )
    ( coe
        ( \v2 v3 ->
            coe
              MAlonzo.Code.Haskell.Prim.du_if_then_else__68
              (coe v1 v3 v2)
              (coe (\v4 -> v3))
              (coe (\v4 -> v2))
        )
    )
    (coe v0)

-- Haskell.Prim.Ord.ordFromLessEq
d_ordFromLessEq_174 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  (AgdaAny -> AgdaAny -> Bool) ->
  T_Ord_36
d_ordFromLessEq_174 ~v0 v1 v2 = du_ordFromLessEq_174 v1 v2
du_ordFromLessEq_174 ::
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  (AgdaAny -> AgdaAny -> Bool) ->
  T_Ord_36
du_ordFromLessEq_174 v0 v1 =
  coe
    C_Ord'46'constructor_505
    ( coe
        ( \v2 v3 ->
            coe
              MAlonzo.Code.Haskell.Prim.du_if_then_else__68
              (coe MAlonzo.Code.Haskell.Prim.Eq.d__'61''61'__14 v0 v2 v3)
              (coe (\v4 -> coe C_EQ_10))
              ( coe
                  ( \v4 ->
                      coe
                        MAlonzo.Code.Haskell.Prim.du_if_then_else__68
                        (coe v1 v2 v3)
                        (coe (\v5 -> coe C_LT_8))
                        (coe (\v5 -> coe C_GT_12))
                  )
              )
        )
    )
    ( coe
        ( \v2 v3 ->
            MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
              (coe v1 v2 v3)
              ( coe
                  MAlonzo.Code.Haskell.Prim.Bool.d_not_14
                  (coe MAlonzo.Code.Haskell.Prim.Eq.d__'61''61'__14 v0 v2 v3)
              )
        )
    )
    ( coe
        ( \v2 v3 ->
            MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
              (coe v1 v3 v2)
              ( coe
                  MAlonzo.Code.Haskell.Prim.Bool.d_not_14
                  (coe MAlonzo.Code.Haskell.Prim.Eq.d__'61''61'__14 v0 v2 v3)
              )
        )
    )
    (coe (\v2 v3 -> coe v1 v3 v2))
    (coe (\v2 v3 -> coe v1 v2 v3))
    ( coe
        ( \v2 v3 ->
            coe
              MAlonzo.Code.Haskell.Prim.du_if_then_else__68
              (coe v1 v3 v2)
              (coe (\v4 -> v2))
              (coe (\v4 -> v3))
        )
    )
    ( coe
        ( \v2 v3 ->
            coe
              MAlonzo.Code.Haskell.Prim.du_if_then_else__68
              (coe v1 v2 v3)
              (coe (\v4 -> v2))
              (coe (\v4 -> v3))
        )
    )
    (coe v0)

-- Haskell.Prim.Ord.maxNat
d_maxNat_226 :: Integer -> Integer -> Integer
d_maxNat_226 v0 v1 =
  case coe v0 of
    0 -> coe v1
    _ ->
      let v2 = subInt (coe v0) (coe (1 :: Integer))
       in coe
            ( case coe v1 of
                0 -> coe v0
                _ ->
                  let v3 = subInt (coe v1) (coe (1 :: Integer))
                   in coe
                        ( coe
                            addInt
                            (coe (1 :: Integer))
                            (coe d_maxNat_226 (coe v2) (coe v3))
                        )
            )

-- Haskell.Prim.Ord.minNat
d_minNat_236 :: Integer -> Integer -> Integer
d_minNat_236 v0 v1 =
  case coe v0 of
    0 -> coe (0 :: Integer)
    _ ->
      let v2 = subInt (coe v0) (coe (1 :: Integer))
       in coe
            ( case coe v1 of
                0 -> coe (0 :: Integer)
                _ ->
                  let v3 = subInt (coe v1) (coe (1 :: Integer))
                   in coe
                        ( coe
                            addInt
                            (coe (1 :: Integer))
                            (coe d_minNat_236 (coe v2) (coe v3))
                        )
            )

-- Haskell.Prim.Ord.iOrdNat
d_iOrdNat_246 :: T_Ord_36
d_iOrdNat_246 =
  coe
    C_Ord'46'constructor_505
    ( coe
        ( \v0 v1 ->
            coe
              MAlonzo.Code.Haskell.Prim.du_if_then_else__68
              (coe ltInt (coe v0) (coe v1))
              (coe (\v2 -> coe C_LT_8))
              ( coe
                  ( \v2 ->
                      coe
                        MAlonzo.Code.Haskell.Prim.du_if_then_else__68
                        (coe eqInt (coe v0) (coe v1))
                        (coe (\v3 -> coe C_EQ_10))
                        (coe (\v3 -> coe C_GT_12))
                  )
              )
        )
    )
    (coe (\v0 v1 -> ltInt (coe v0) (coe v1)))
    (coe (\v0 v1 -> ltInt (coe v1) (coe v0)))
    ( coe
        ( \v0 v1 ->
            MAlonzo.Code.Haskell.Prim.Bool.d__'124''124'__10
              (coe ltInt (coe v1) (coe v0))
              (coe eqInt (coe v0) (coe v1))
        )
    )
    ( coe
        ( \v0 v1 ->
            MAlonzo.Code.Haskell.Prim.Bool.d__'124''124'__10
              (coe ltInt (coe v0) (coe v1))
              (coe eqInt (coe v0) (coe v1))
        )
    )
    (coe d_maxNat_226)
    (coe d_minNat_236)
    (coe MAlonzo.Code.Haskell.Prim.Eq.d_iEqNat_28)

-- Haskell.Prim.Ord.iOrdInteger
d_iOrdInteger_248 :: T_Ord_36
d_iOrdInteger_248 =
  coe
    du_ordFromLessThan_130
    (coe MAlonzo.Code.Haskell.Prim.Eq.d_iEqInteger_30)
    (coe MAlonzo.Code.Haskell.Prim.Integer.d_ltInteger_90)

-- Haskell.Prim.Ord.iOrdInt
d_iOrdInt_250 :: T_Ord_36
d_iOrdInt_250 =
  coe
    du_ordFromLessThan_130
    (coe MAlonzo.Code.Haskell.Prim.Eq.d_iEqInt_32)
    (coe MAlonzo.Code.Haskell.Prim.Int.d_ltInt_66)

-- Haskell.Prim.Ord.iOrdWord
d_iOrdWord_252 :: T_Ord_36
d_iOrdWord_252 =
  coe
    du_ordFromLessThan_130
    (coe MAlonzo.Code.Haskell.Prim.Eq.d_iEqWord_34)
    (coe MAlonzo.Code.Haskell.Prim.Word.d_ltWord_42)

-- Haskell.Prim.Ord.iOrdDouble
d_iOrdDouble_254 :: T_Ord_36
d_iOrdDouble_254 =
  coe
    du_ordFromLessThan_130
    (coe MAlonzo.Code.Haskell.Prim.Eq.d_iEqDouble_36)
    (coe MAlonzo.Code.Agda.Builtin.Float.d_primFloatLess_12)

-- Haskell.Prim.Ord.iOrdChar
d_iOrdChar_256 :: T_Ord_36
d_iOrdChar_256 =
  coe
    du_ordFromLessThan_130
    (coe MAlonzo.Code.Haskell.Prim.Eq.d_iEqChar_40)
    ( coe
        ( \v0 v1 ->
            coe
              d__'60'__58
              d_iOrdNat_246
              (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v0)
              (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v1)
        )
    )

-- Haskell.Prim.Ord.iOrdBool
d_iOrdBool_262 :: T_Ord_36
d_iOrdBool_262 =
  coe
    du_ordFromCompare_90
    (coe MAlonzo.Code.Haskell.Prim.Eq.d_iEqBool_38)
    ( coe
        ( \v0 v1 ->
            let v2 = coe C_EQ_10
             in coe
                  ( if coe v0
                      then case coe v1 of
                        MAlonzo.Code.Agda.Builtin.Bool.C_false_8 -> coe C_GT_12
                        _ -> coe v2
                      else
                        ( case coe v1 of
                            MAlonzo.Code.Agda.Builtin.Bool.C_true_10 -> coe C_LT_8
                            _ -> coe v2
                        )
                  )
        )
    )

-- Haskell.Prim.Ord.iOrdUnit
d_iOrdUnit_266 :: T_Ord_36
d_iOrdUnit_266 =
  coe
    du_ordFromCompare_90
    (coe MAlonzo.Code.Haskell.Prim.Eq.d_iEqUnit_42)
    (coe (\v0 v1 -> coe C_EQ_10))

-- Haskell.Prim.Ord.iOrdTuple₂
d_iOrdTuple'8322'_272 ::
  () -> () -> T_Ord_36 -> T_Ord_36 -> T_Ord_36
d_iOrdTuple'8322'_272 ~v0 ~v1 v2 v3 = du_iOrdTuple'8322'_272 v2 v3
du_iOrdTuple'8322'_272 :: T_Ord_36 -> T_Ord_36 -> T_Ord_36
du_iOrdTuple'8322'_272 v0 v1 =
  coe
    du_ordFromCompare_90
    ( coe
        MAlonzo.Code.Haskell.Prim.Eq.du_iEqTuple'8322'_44
        (coe d_super_70 (coe v0))
        (coe d_super_70 (coe v1))
    )
    ( coe
        ( \v2 v3 ->
            case coe v2 of
              MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24 v4 v5 ->
                case coe v3 of
                  MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24 v6 v7 ->
                    coe
                      MAlonzo.Code.Haskell.Prim.Monoid.d__'60''62'__14
                      d_iSemigroupOrdering_16
                      (coe d_compare_56 v0 v4 v6)
                      (coe d_compare_56 v1 v5 v7)
                  _ -> MAlonzo.RTE.mazUnreachableError
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )

-- Haskell.Prim.Ord.iOrdTuple₃
d_iOrdTuple'8323'_284 ::
  () -> () -> () -> T_Ord_36 -> T_Ord_36 -> T_Ord_36 -> T_Ord_36
d_iOrdTuple'8323'_284 ~v0 ~v1 ~v2 v3 v4 v5 =
  du_iOrdTuple'8323'_284 v3 v4 v5
du_iOrdTuple'8323'_284 ::
  T_Ord_36 -> T_Ord_36 -> T_Ord_36 -> T_Ord_36
du_iOrdTuple'8323'_284 v0 v1 v2 =
  coe
    du_ordFromCompare_90
    ( coe
        MAlonzo.Code.Haskell.Prim.Eq.du_iEqTuple'8323'_54
        (coe d_super_70 (coe v0))
        (coe d_super_70 (coe v1))
        (coe d_super_70 (coe v2))
    )
    ( coe
        ( \v3 v4 ->
            case coe v3 of
              MAlonzo.Code.Haskell.Prim.Tuple.C__'44'_'44'__40 v5 v6 v7 ->
                case coe v4 of
                  MAlonzo.Code.Haskell.Prim.Tuple.C__'44'_'44'__40 v8 v9 v10 ->
                    coe
                      MAlonzo.Code.Haskell.Prim.Monoid.d__'60''62'__14
                      d_iSemigroupOrdering_16
                      (coe d_compare_56 v0 v5 v8)
                      ( coe
                          MAlonzo.Code.Haskell.Prim.Monoid.d__'60''62'__14
                          d_iSemigroupOrdering_16
                          (coe d_compare_56 v1 v6 v9)
                          (coe d_compare_56 v2 v7 v10)
                      )
                  _ -> MAlonzo.RTE.mazUnreachableError
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )

-- Haskell.Prim.Ord.compareList
d_compareList_300 ::
  () -> T_Ord_36 -> [AgdaAny] -> [AgdaAny] -> T_Ordering_6
d_compareList_300 ~v0 v1 v2 v3 = du_compareList_300 v1 v2 v3
du_compareList_300 ::
  T_Ord_36 -> [AgdaAny] -> [AgdaAny] -> T_Ordering_6
du_compareList_300 v0 v1 v2 =
  case coe v1 of
    [] ->
      case coe v2 of
        [] -> coe C_EQ_10
        (:) v3 v4 -> coe C_LT_8
        _ -> MAlonzo.RTE.mazUnreachableError
    (:) v3 v4 ->
      case coe v2 of
        [] -> coe C_GT_12
        (:) v5 v6 ->
          coe
            MAlonzo.Code.Haskell.Prim.Monoid.d__'60''62'__14
            d_iSemigroupOrdering_16
            (coe d_compare_56 v0 v3 v5)
            (coe du_compareList_300 (coe v0) (coe v4) (coe v6))
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Ord.iOrdList
d_iOrdList_310 :: () -> T_Ord_36 -> T_Ord_36
d_iOrdList_310 ~v0 v1 = du_iOrdList_310 v1
du_iOrdList_310 :: T_Ord_36 -> T_Ord_36
du_iOrdList_310 v0 =
  coe
    du_ordFromCompare_90
    ( coe
        MAlonzo.Code.Haskell.Prim.Eq.du_iEqList_68
        (coe d_super_70 (coe v0))
    )
    (coe du_compareList_300 (coe v0))

-- Haskell.Prim.Ord.iOrdMaybe
d_iOrdMaybe_312 :: () -> T_Ord_36 -> T_Ord_36
d_iOrdMaybe_312 ~v0 v1 = du_iOrdMaybe_312 v1
du_iOrdMaybe_312 :: T_Ord_36 -> T_Ord_36
du_iOrdMaybe_312 v0 =
  coe
    du_ordFromCompare_90
    ( coe
        MAlonzo.Code.Haskell.Prim.Eq.du_iEqMaybe_86
        (coe d_super_70 (coe v0))
    )
    ( coe
        ( \v1 v2 ->
            case coe v1 of
              MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16 ->
                case coe v2 of
                  MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16 -> coe C_EQ_10
                  MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 v3 -> coe C_LT_8
                  _ -> MAlonzo.RTE.mazUnreachableError
              MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 v3 ->
                case coe v2 of
                  MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16 -> coe C_GT_12
                  MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 v4 ->
                    coe d_compare_56 v0 v3 v4
                  _ -> MAlonzo.RTE.mazUnreachableError
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )

-- Haskell.Prim.Ord.iOrdEither
d_iOrdEither_320 :: () -> () -> T_Ord_36 -> T_Ord_36 -> T_Ord_36
d_iOrdEither_320 ~v0 ~v1 v2 v3 = du_iOrdEither_320 v2 v3
du_iOrdEither_320 :: T_Ord_36 -> T_Ord_36 -> T_Ord_36
du_iOrdEither_320 v0 v1 =
  coe
    du_ordFromCompare_90
    ( coe
        MAlonzo.Code.Haskell.Prim.Eq.du_iEqEither_92
        (coe d_super_70 (coe v0))
        (coe d_super_70 (coe v1))
    )
    ( coe
        ( \v2 v3 ->
            case coe v2 of
              MAlonzo.Code.Haskell.Prim.Either.C_Left_16 v4 ->
                case coe v3 of
                  MAlonzo.Code.Haskell.Prim.Either.C_Left_16 v5 ->
                    coe d_compare_56 v0 v4 v5
                  MAlonzo.Code.Haskell.Prim.Either.C_Right_18 v5 -> coe C_LT_8
                  _ -> MAlonzo.RTE.mazUnreachableError
              MAlonzo.Code.Haskell.Prim.Either.C_Right_18 v4 ->
                case coe v3 of
                  MAlonzo.Code.Haskell.Prim.Either.C_Left_16 v5 -> coe C_GT_12
                  MAlonzo.Code.Haskell.Prim.Either.C_Right_18 v5 ->
                    coe d_compare_56 v1 v4 v5
                  _ -> MAlonzo.RTE.mazUnreachableError
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )

-- Haskell.Prim.Ord.iOrdOrdering
d_iOrdOrdering_332 :: T_Ord_36
d_iOrdOrdering_332 =
  coe
    du_ordFromCompare_90
    (coe d_iEqOrdering_14)
    ( coe
        ( \v0 v1 ->
            case coe v0 of
              C_LT_8 ->
                case coe v1 of
                  C_LT_8 -> coe C_EQ_10
                  _ -> coe v0
              C_EQ_10 ->
                case coe v1 of
                  C_LT_8 -> coe C_GT_12
                  C_EQ_10 -> coe v1
                  C_GT_12 -> coe C_LT_8
                  _ -> MAlonzo.RTE.mazUnreachableError
              C_GT_12 ->
                case coe v1 of
                  C_LT_8 -> coe v0
                  C_EQ_10 -> coe v0
                  C_GT_12 -> coe C_EQ_10
                  _ -> MAlonzo.RTE.mazUnreachableError
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )
