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

module MAlonzo.Code.Haskell.Prim.Enum where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Haskell.Prim
import qualified MAlonzo.Code.Haskell.Prim.Bounded
import qualified MAlonzo.Code.Haskell.Prim.Eq
import qualified MAlonzo.Code.Haskell.Prim.Int
import qualified MAlonzo.Code.Haskell.Prim.Integer
import qualified MAlonzo.Code.Haskell.Prim.List
import qualified MAlonzo.Code.Haskell.Prim.Maybe
import qualified MAlonzo.Code.Haskell.Prim.Ord
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

-- Haskell.Prim.Enum.IfBoundedBelow
d_IfBoundedBelow_6 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10 ->
  (MAlonzo.Code.Haskell.Prim.Bounded.T_BoundedBelow_8 -> ()) ->
  ()
d_IfBoundedBelow_6 = erased

-- Haskell.Prim.Enum.IfBoundedAbove
d_IfBoundedAbove_14 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10 ->
  (MAlonzo.Code.Haskell.Prim.Bounded.T_BoundedAbove_18 -> ()) ->
  ()
d_IfBoundedAbove_14 = erased

-- Haskell.Prim.Enum.Enum
d_Enum_24 a0 = ()
data T_Enum_24
  = C_Enum'46'constructor_3155
      MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10
      MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10
      (AgdaAny -> MAlonzo.Code.Haskell.Prim.Int.T_Int_6)
      ( MAlonzo.Code.Haskell.Prim.Int.T_Int_6 ->
        AgdaAny ->
        AgdaAny ->
        AgdaAny
      )
      (AgdaAny -> AgdaAny -> AgdaAny)
      (AgdaAny -> AgdaAny -> AgdaAny)
      (AgdaAny -> AgdaAny -> [AgdaAny])
      (AgdaAny -> AgdaAny -> [AgdaAny])
      ( AgdaAny ->
        AgdaAny ->
        MAlonzo.Code.Haskell.Prim.T_IsFalse_130 ->
        AgdaAny ->
        [AgdaAny]
      )
      ( AgdaAny ->
        AgdaAny ->
        AgdaAny ->
        AgdaAny ->
        MAlonzo.Code.Haskell.Prim.T_IsFalse_130 ->
        [AgdaAny]
      )

-- Haskell.Prim.Enum.Enum.BoundedBelowEnum
d_BoundedBelowEnum_94 ::
  T_Enum_24 -> MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10
d_BoundedBelowEnum_94 v0 =
  case coe v0 of
    C_Enum'46'constructor_3155 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Enum.Enum.BoundedAboveEnum
d_BoundedAboveEnum_96 ::
  T_Enum_24 -> MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10
d_BoundedAboveEnum_96 v0 =
  case coe v0 of
    C_Enum'46'constructor_3155 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Enum.Enum.fromEnum
d_fromEnum_98 ::
  T_Enum_24 -> AgdaAny -> MAlonzo.Code.Haskell.Prim.Int.T_Int_6
d_fromEnum_98 v0 =
  case coe v0 of
    C_Enum'46'constructor_3155 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Enum.Enum.toEnum
d_toEnum_130 ::
  T_Enum_24 ->
  MAlonzo.Code.Haskell.Prim.Int.T_Int_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d_toEnum_130 v0 =
  case coe v0 of
    C_Enum'46'constructor_3155 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v4
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Enum.Enum.succ
d_succ_134 :: T_Enum_24 -> AgdaAny -> AgdaAny -> AgdaAny
d_succ_134 v0 =
  case coe v0 of
    C_Enum'46'constructor_3155 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v5
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Enum.Enum.pred
d_pred_138 :: T_Enum_24 -> AgdaAny -> AgdaAny -> AgdaAny
d_pred_138 v0 =
  case coe v0 of
    C_Enum'46'constructor_3155 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v6
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Enum.Enum.enumFrom
d_enumFrom_140 :: T_Enum_24 -> AgdaAny -> AgdaAny -> [AgdaAny]
d_enumFrom_140 v0 =
  case coe v0 of
    C_Enum'46'constructor_3155 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v7
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Enum.Enum.enumFromTo
d_enumFromTo_142 :: T_Enum_24 -> AgdaAny -> AgdaAny -> [AgdaAny]
d_enumFromTo_142 v0 =
  case coe v0 of
    C_Enum'46'constructor_3155 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v8
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Enum.Enum.enumFromThenTo
d_enumFromThenTo_148 ::
  T_Enum_24 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Haskell.Prim.T_IsFalse_130 ->
  AgdaAny ->
  [AgdaAny]
d_enumFromThenTo_148 v0 =
  case coe v0 of
    C_Enum'46'constructor_3155 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v9
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Enum.Enum.enumFromThen
d_enumFromThen_154 ::
  T_Enum_24 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Haskell.Prim.T_IsFalse_130 ->
  [AgdaAny]
d_enumFromThen_154 v0 =
  case coe v0 of
    C_Enum'46'constructor_3155 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ->
      coe v10
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Enum._.BoundedAboveEnum
d_BoundedAboveEnum_158 ::
  T_Enum_24 -> MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10
d_BoundedAboveEnum_158 v0 = coe d_BoundedAboveEnum_96 (coe v0)

-- Haskell.Prim.Enum._.BoundedBelowEnum
d_BoundedBelowEnum_160 ::
  T_Enum_24 -> MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10
d_BoundedBelowEnum_160 v0 = coe d_BoundedBelowEnum_94 (coe v0)

-- Haskell.Prim.Enum._.enumFrom
d_enumFrom_162 :: T_Enum_24 -> AgdaAny -> AgdaAny -> [AgdaAny]
d_enumFrom_162 v0 = coe d_enumFrom_140 (coe v0)

-- Haskell.Prim.Enum._.enumFromThen
d_enumFromThen_164 ::
  T_Enum_24 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Haskell.Prim.T_IsFalse_130 ->
  [AgdaAny]
d_enumFromThen_164 v0 = coe d_enumFromThen_154 (coe v0)

-- Haskell.Prim.Enum._.enumFromThenTo
d_enumFromThenTo_166 ::
  T_Enum_24 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Haskell.Prim.T_IsFalse_130 ->
  AgdaAny ->
  [AgdaAny]
d_enumFromThenTo_166 v0 = coe d_enumFromThenTo_148 (coe v0)

-- Haskell.Prim.Enum._.enumFromTo
d_enumFromTo_168 :: T_Enum_24 -> AgdaAny -> AgdaAny -> [AgdaAny]
d_enumFromTo_168 v0 = coe d_enumFromTo_142 (coe v0)

-- Haskell.Prim.Enum._.fromEnum
d_fromEnum_170 ::
  T_Enum_24 -> AgdaAny -> MAlonzo.Code.Haskell.Prim.Int.T_Int_6
d_fromEnum_170 v0 = coe d_fromEnum_98 (coe v0)

-- Haskell.Prim.Enum._.pred
d_pred_172 :: T_Enum_24 -> AgdaAny -> AgdaAny -> AgdaAny
d_pred_172 v0 = coe d_pred_138 (coe v0)

-- Haskell.Prim.Enum._.succ
d_succ_174 :: T_Enum_24 -> AgdaAny -> AgdaAny -> AgdaAny
d_succ_174 v0 = coe d_succ_134 (coe v0)

-- Haskell.Prim.Enum._.toEnum
d_toEnum_176 ::
  T_Enum_24 ->
  MAlonzo.Code.Haskell.Prim.Int.T_Int_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d_toEnum_176 v0 = coe d_toEnum_130 (coe v0)

-- Haskell.Prim.Enum.divNat
d_divNat_178 :: Integer -> Integer -> Integer
d_divNat_178 v0 v1 =
  case coe v1 of
    0 -> coe (0 :: Integer)
    _ -> coe quotInt (coe v0) (coe v1)

-- Haskell.Prim.Enum.diff
d_diff_186 ::
  Integer -> Integer -> MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10
d_diff_186 v0 v1 =
  coe
    MAlonzo.Code.Haskell.Prim.du_case_of__58
    ( coe
        MAlonzo.Code.Haskell.Prim.Integer.d_subInteger_48
        (coe v0)
        (coe v1)
    )
    ( coe
        ( \v2 v3 ->
            case coe v2 of
              _
                | coe geqInt (coe v2) (coe (0 :: Integer)) ->
                    coe MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 (coe v2)
              _ -> coe MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16
        )
    )

-- Haskell.Prim.Enum.unsafeIntegerToNat
d_unsafeIntegerToNat_196 :: Integer -> Integer
d_unsafeIntegerToNat_196 v0 =
  case coe v0 of
    _ | coe geqInt (coe v0) (coe (0 :: Integer)) -> coe v0
    _ -> coe (0 :: Integer)

-- Haskell.Prim.Enum.integerFromCount
d_integerFromCount_200 ::
  Integer -> Integer -> Integer -> [Integer]
d_integerFromCount_200 v0 v1 v2 =
  case coe v2 of
    0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
    _ ->
      let v3 = subInt (coe v2) (coe (1 :: Integer))
       in coe
            ( coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe v0)
                ( coe
                    d_integerFromCount_200
                    ( coe
                        MAlonzo.Code.Haskell.Prim.Integer.d_addInteger_30
                        (coe v0)
                        (coe v1)
                    )
                    (coe v1)
                    (coe v3)
                )
            )

-- Haskell.Prim.Enum.integerFromTo
d_integerFromTo_212 :: Integer -> Integer -> [Integer]
d_integerFromTo_212 v0 v1 =
  coe
    MAlonzo.Code.Haskell.Prim.Maybe.du_maybe_28
    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
    ( coe
        MAlonzo.Code.Haskell.Prim.du__'8728'__28
        (coe d_integerFromCount_200 (coe v0) (coe (1 :: Integer)))
        (coe (\v2 -> addInt (coe (1 :: Integer)) (coe v2)))
    )
    (coe d_diff_186 (coe v1) (coe v0))

-- Haskell.Prim.Enum.integerFromThenTo
d_integerFromThenTo_222 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Haskell.Prim.T_IsFalse_130 ->
  Integer ->
  [Integer]
d_integerFromThenTo_222 v0 v1 ~v2 v3 =
  du_integerFromThenTo_222 v0 v1 v3
du_integerFromThenTo_222 ::
  Integer -> Integer -> Integer -> [Integer]
du_integerFromThenTo_222 v0 v1 v2 =
  coe
    MAlonzo.Code.Haskell.Prim.du_case_of__58
    ( coe
        MAlonzo.Code.Haskell.Prim.du_if_then_else__68
        ( coe
            MAlonzo.Code.Haskell.Prim.Integer.d_ltInteger_90
            (coe v0)
            (coe v1)
        )
        (coe (\v3 -> coe MAlonzo.Code.Haskell.Prim.Ord.C_LT_8))
        ( coe
            ( \v3 ->
                coe
                  MAlonzo.Code.Haskell.Prim.du_if_then_else__68
                  ( coe
                      MAlonzo.Code.Haskell.Prim.Integer.d_eqInteger_80
                      (coe v0)
                      (coe v1)
                  )
                  (coe (\v4 -> coe MAlonzo.Code.Haskell.Prim.Ord.C_EQ_10))
                  (coe (\v4 -> coe MAlonzo.Code.Haskell.Prim.Ord.C_GT_12))
            )
        )
    )
    ( coe
        ( \v3 v4 ->
            case coe v3 of
              MAlonzo.Code.Haskell.Prim.Ord.C_LT_8 ->
                coe
                  MAlonzo.Code.Haskell.Prim.Maybe.du_maybe_28
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                  ( coe
                      ( \v5 ->
                          d_integerFromCount_200
                            (coe v0)
                            ( coe
                                MAlonzo.Code.Haskell.Prim.Integer.d_subInteger_48
                                (coe v1)
                                (coe v0)
                            )
                            ( coe
                                addInt
                                (coe (1 :: Integer))
                                ( coe
                                    d_divNat_178
                                    (coe v5)
                                    ( coe
                                        d_unsafeIntegerToNat_196
                                        ( coe
                                            MAlonzo.Code.Haskell.Prim.Integer.d_subInteger_48
                                            (coe v1)
                                            (coe v0)
                                        )
                                    )
                                )
                            )
                      )
                  )
                  (coe d_diff_186 (coe v2) (coe v0))
              MAlonzo.Code.Haskell.Prim.Ord.C_EQ_10 ->
                coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
              MAlonzo.Code.Haskell.Prim.Ord.C_GT_12 ->
                coe
                  MAlonzo.Code.Haskell.Prim.Maybe.du_maybe_28
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                  ( coe
                      ( \v5 ->
                          d_integerFromCount_200
                            (coe v0)
                            ( coe
                                MAlonzo.Code.Haskell.Prim.Integer.d_subInteger_48
                                (coe v1)
                                (coe v0)
                            )
                            ( coe
                                addInt
                                (coe (1 :: Integer))
                                ( coe
                                    d_divNat_178
                                    (coe v5)
                                    ( coe
                                        d_unsafeIntegerToNat_196
                                        ( coe
                                            MAlonzo.Code.Haskell.Prim.Integer.d_subInteger_48
                                            (coe v0)
                                            (coe v1)
                                        )
                                    )
                                )
                            )
                      )
                  )
                  (coe d_diff_186 (coe v0) (coe v2))
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )

-- Haskell.Prim.Enum.iEnumInteger
d_iEnumInteger_236 :: T_Enum_24
d_iEnumInteger_236 =
  coe
    C_Enum'46'constructor_3155
    (coe MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16)
    (coe MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16)
    (coe MAlonzo.Code.Haskell.Prim.Int.d_integerToInt_54)
    ( coe
        ( \v0 v1 v2 ->
            MAlonzo.Code.Haskell.Prim.Int.d_intToInteger_50 (coe v0)
        )
    )
    ( coe
        ( \v0 v1 ->
            MAlonzo.Code.Haskell.Prim.Integer.d_addInteger_30
              (coe v0)
              (coe (1 :: Integer))
        )
    )
    ( coe
        ( \v0 v1 ->
            MAlonzo.Code.Haskell.Prim.Integer.d_subInteger_48
              (coe v0)
              (coe (1 :: Integer))
        )
    )
    (coe (\v0 v1 -> MAlonzo.RTE.mazUnreachableError))
    (coe d_integerFromTo_212)
    (\v0 v1 v2 v3 -> coe du_integerFromThenTo_222 v0 v1 v3)
    (coe (\v0 v1 v2 v3 v4 -> MAlonzo.RTE.mazUnreachableError))

-- Haskell.Prim.Enum._.fromTo
d_fromTo_254 ::
  () ->
  (AgdaAny -> Integer) ->
  (Integer -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny]
d_fromTo_254 ~v0 v1 v2 v3 v4 = du_fromTo_254 v1 v2 v3 v4
du_fromTo_254 ::
  (AgdaAny -> Integer) ->
  (Integer -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny]
du_fromTo_254 v0 v1 v2 v3 =
  coe
    MAlonzo.Code.Haskell.Prim.List.du_map_6
    (coe v1)
    (coe d_integerFromTo_212 (coe v0 v2) (coe v0 v3))

-- Haskell.Prim.Enum._.fromThenTo
d_fromThenTo_264 ::
  () ->
  (AgdaAny -> Integer) ->
  (Integer -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Haskell.Prim.T_IsFalse_130 ->
  AgdaAny ->
  [AgdaAny]
d_fromThenTo_264 ~v0 v1 v2 v3 v4 ~v5 v6 =
  du_fromThenTo_264 v1 v2 v3 v4 v6
du_fromThenTo_264 ::
  (AgdaAny -> Integer) ->
  (Integer -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny]
du_fromThenTo_264 v0 v1 v2 v3 v4 =
  coe
    MAlonzo.Code.Haskell.Prim.List.du_map_6
    (coe v1)
    (coe du_integerFromThenTo_222 (coe v0 v2) (coe v0 v3) (coe v0 v4))

-- Haskell.Prim.Enum._.unboundedEnumViaInteger
d_unboundedEnumViaInteger_272 ::
  () -> (AgdaAny -> Integer) -> (Integer -> AgdaAny) -> T_Enum_24
d_unboundedEnumViaInteger_272 ~v0 v1 v2 =
  du_unboundedEnumViaInteger_272 v1 v2
du_unboundedEnumViaInteger_272 ::
  (AgdaAny -> Integer) -> (Integer -> AgdaAny) -> T_Enum_24
du_unboundedEnumViaInteger_272 v0 v1 =
  coe
    C_Enum'46'constructor_3155
    (coe MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16)
    (coe MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16)
    ( coe
        MAlonzo.Code.Haskell.Prim.du__'8728'__28
        (coe MAlonzo.Code.Haskell.Prim.Int.d_integerToInt_54)
        (coe v0)
    )
    ( coe
        ( \v2 v3 v4 ->
            coe v1 (MAlonzo.Code.Haskell.Prim.Int.d_intToInteger_50 (coe v2))
        )
    )
    ( coe
        ( \v2 v3 ->
            coe
              v1
              ( MAlonzo.Code.Haskell.Prim.Integer.d_addInteger_30
                  (coe v0 v2)
                  (coe (1 :: Integer))
              )
        )
    )
    ( coe
        ( \v2 v3 ->
            coe
              v1
              ( MAlonzo.Code.Haskell.Prim.Integer.d_subInteger_48
                  (coe v0 v2)
                  (coe (1 :: Integer))
              )
        )
    )
    (coe (\v2 v3 -> MAlonzo.RTE.mazUnreachableError))
    ( coe
        (\v2 v3 -> coe du_fromTo_254 (coe v0) (coe v1) (coe v2) (coe v3))
    )
    ( coe
        ( \v2 v3 v4 v5 ->
            coe
              du_fromThenTo_264
              (coe v0)
              (coe v1)
              (coe v2)
              (coe v3)
              (coe v5)
        )
    )
    (coe (\v2 v3 v4 v5 v6 -> MAlonzo.RTE.mazUnreachableError))

-- Haskell.Prim.Enum._.boundedBelowEnumViaInteger
d_boundedBelowEnumViaInteger_290 ::
  () ->
  (AgdaAny -> Integer) ->
  (Integer -> AgdaAny) ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  MAlonzo.Code.Haskell.Prim.Bounded.T_BoundedBelow_8 ->
  T_Enum_24
d_boundedBelowEnumViaInteger_290 ~v0 v1 v2 ~v3 v4 =
  du_boundedBelowEnumViaInteger_290 v1 v2 v4
du_boundedBelowEnumViaInteger_290 ::
  (AgdaAny -> Integer) ->
  (Integer -> AgdaAny) ->
  MAlonzo.Code.Haskell.Prim.Bounded.T_BoundedBelow_8 ->
  T_Enum_24
du_boundedBelowEnumViaInteger_290 v0 v1 v2 =
  coe
    C_Enum'46'constructor_3155
    (coe MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 (coe v2))
    (coe MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16)
    ( coe
        MAlonzo.Code.Haskell.Prim.du__'8728'__28
        (coe MAlonzo.Code.Haskell.Prim.Int.d_integerToInt_54)
        (coe v0)
    )
    ( coe
        ( \v3 v4 v5 ->
            coe v1 (MAlonzo.Code.Haskell.Prim.Int.d_intToInteger_50 (coe v3))
        )
    )
    ( coe
        ( \v3 v4 ->
            coe
              v1
              ( MAlonzo.Code.Haskell.Prim.Integer.d_addInteger_30
                  (coe v0 v3)
                  (coe (1 :: Integer))
              )
        )
    )
    ( coe
        ( \v3 v4 ->
            coe
              v1
              ( MAlonzo.Code.Haskell.Prim.Integer.d_subInteger_48
                  (coe v0 v3)
                  (coe (1 :: Integer))
              )
        )
    )
    (coe (\v3 v4 -> MAlonzo.RTE.mazUnreachableError))
    ( coe
        (\v3 v4 -> coe du_fromTo_254 (coe v0) (coe v1) (coe v3) (coe v4))
    )
    ( coe
        ( \v3 v4 v5 v6 ->
            coe
              du_fromThenTo_264
              (coe v0)
              (coe v1)
              (coe v3)
              (coe v4)
              (coe v6)
        )
    )
    (coe (\v3 v4 v5 v6 v7 -> MAlonzo.RTE.mazUnreachableError))

-- Haskell.Prim.Enum._.boundedAboveEnumViaInteger
d_boundedAboveEnumViaInteger_308 ::
  () ->
  (AgdaAny -> Integer) ->
  (Integer -> AgdaAny) ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  MAlonzo.Code.Haskell.Prim.Bounded.T_BoundedAbove_18 ->
  T_Enum_24
d_boundedAboveEnumViaInteger_308 ~v0 v1 v2 ~v3 v4 =
  du_boundedAboveEnumViaInteger_308 v1 v2 v4
du_boundedAboveEnumViaInteger_308 ::
  (AgdaAny -> Integer) ->
  (Integer -> AgdaAny) ->
  MAlonzo.Code.Haskell.Prim.Bounded.T_BoundedAbove_18 ->
  T_Enum_24
du_boundedAboveEnumViaInteger_308 v0 v1 v2 =
  coe
    C_Enum'46'constructor_3155
    (coe MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16)
    (coe MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 (coe v2))
    ( coe
        MAlonzo.Code.Haskell.Prim.du__'8728'__28
        (coe MAlonzo.Code.Haskell.Prim.Int.d_integerToInt_54)
        (coe v0)
    )
    ( coe
        ( \v3 v4 v5 ->
            coe v1 (MAlonzo.Code.Haskell.Prim.Int.d_intToInteger_50 (coe v3))
        )
    )
    ( coe
        ( \v3 v4 ->
            coe
              v1
              ( MAlonzo.Code.Haskell.Prim.Integer.d_addInteger_30
                  (coe v0 v3)
                  (coe (1 :: Integer))
              )
        )
    )
    ( coe
        ( \v3 v4 ->
            coe
              v1
              ( MAlonzo.Code.Haskell.Prim.Integer.d_subInteger_48
                  (coe v0 v3)
                  (coe (1 :: Integer))
              )
        )
    )
    ( coe
        ( \v3 v4 ->
            coe
              du_fromTo_254
              (coe v0)
              (coe v1)
              (coe v4)
              (coe MAlonzo.Code.Haskell.Prim.Bounded.d_maxBound_24 (coe v2))
        )
    )
    ( coe
        (\v3 v4 -> coe du_fromTo_254 (coe v0) (coe v1) (coe v3) (coe v4))
    )
    ( coe
        ( \v3 v4 v5 v6 ->
            coe
              du_fromThenTo_264
              (coe v0)
              (coe v1)
              (coe v3)
              (coe v4)
              (coe v6)
        )
    )
    (coe (\v3 v4 v5 v6 v7 -> MAlonzo.RTE.mazUnreachableError))

-- Haskell.Prim.Enum._.boundedEnumViaInteger
d_boundedEnumViaInteger_328 ::
  () ->
  (AgdaAny -> Integer) ->
  (Integer -> AgdaAny) ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  MAlonzo.Code.Haskell.Prim.Bounded.T_Bounded_28 ->
  T_Enum_24
d_boundedEnumViaInteger_328 ~v0 v1 v2 v3 v4 =
  du_boundedEnumViaInteger_328 v1 v2 v3 v4
du_boundedEnumViaInteger_328 ::
  (AgdaAny -> Integer) ->
  (Integer -> AgdaAny) ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  MAlonzo.Code.Haskell.Prim.Bounded.T_Bounded_28 ->
  T_Enum_24
du_boundedEnumViaInteger_328 v0 v1 v2 v3 =
  coe
    C_Enum'46'constructor_3155
    ( coe
        MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18
        (coe MAlonzo.Code.Haskell.Prim.Bounded.d_below_36 (coe v3))
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18
        (coe MAlonzo.Code.Haskell.Prim.Bounded.d_above_38 (coe v3))
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.du__'8728'__28
        (coe MAlonzo.Code.Haskell.Prim.Int.d_integerToInt_54)
        (coe v0)
    )
    ( coe
        ( \v4 v5 v6 ->
            coe v1 (MAlonzo.Code.Haskell.Prim.Int.d_intToInteger_50 (coe v4))
        )
    )
    ( coe
        ( \v4 v5 ->
            coe
              v1
              ( MAlonzo.Code.Haskell.Prim.Integer.d_addInteger_30
                  (coe v0 v4)
                  (coe (1 :: Integer))
              )
        )
    )
    ( coe
        ( \v4 v5 ->
            coe
              v1
              ( MAlonzo.Code.Haskell.Prim.Integer.d_subInteger_48
                  (coe v0 v4)
                  (coe (1 :: Integer))
              )
        )
    )
    ( coe
        ( \v4 v5 ->
            coe
              du_fromTo_254
              (coe v0)
              (coe v1)
              (coe v5)
              ( coe
                  MAlonzo.Code.Haskell.Prim.Bounded.d_maxBound_24
                  (coe MAlonzo.Code.Haskell.Prim.Bounded.d_above_38 (coe v3))
              )
        )
    )
    ( coe
        (\v4 v5 -> coe du_fromTo_254 (coe v0) (coe v1) (coe v4) (coe v5))
    )
    ( coe
        ( \v4 v5 v6 v7 ->
            coe
              du_fromThenTo_264
              (coe v0)
              (coe v1)
              (coe v4)
              (coe v5)
              (coe v7)
        )
    )
    ( coe
        ( \v4 v5 v6 v7 v8 ->
            coe
              MAlonzo.Code.Haskell.Prim.du_if_then_else__68
              (coe MAlonzo.Code.Haskell.Prim.Ord.d__'60'__58 v2 v6 v7)
              ( coe
                  ( \v9 ->
                      coe
                        du_fromThenTo_264
                        (coe v0)
                        (coe v1)
                        (coe v6)
                        (coe v7)
                        ( coe
                            MAlonzo.Code.Haskell.Prim.Bounded.d_maxBound_24
                            (coe MAlonzo.Code.Haskell.Prim.Bounded.d_above_38 (coe v3))
                        )
                  )
              )
              ( coe
                  ( \v9 ->
                      coe
                        du_fromThenTo_264
                        (coe v0)
                        (coe v1)
                        (coe v6)
                        (coe v7)
                        ( coe
                            MAlonzo.Code.Haskell.Prim.Bounded.d_minBound_14
                            (coe MAlonzo.Code.Haskell.Prim.Bounded.d_below_36 (coe v3))
                        )
                  )
              )
        )
    )

-- Haskell.Prim.Enum.iEnumNat
d_iEnumNat_352 :: T_Enum_24
d_iEnumNat_352 =
  coe
    du_boundedBelowEnumViaInteger_290
    (coe (\v0 -> v0))
    (coe d_unsafeIntegerToNat_196)
    (coe MAlonzo.Code.Haskell.Prim.Bounded.d_iBoundedBelowNat_50)

-- Haskell.Prim.Enum.iEnumInt
d_iEnumInt_354 :: T_Enum_24
d_iEnumInt_354 =
  coe
    du_boundedEnumViaInteger_328
    (coe MAlonzo.Code.Haskell.Prim.Int.d_intToInteger_50)
    (coe MAlonzo.Code.Haskell.Prim.Int.d_integerToInt_54)
    ( coe
        MAlonzo.Code.Haskell.Prim.Ord.du_ordFromLessThan_130
        (coe MAlonzo.Code.Haskell.Prim.Eq.d_iEqInt_32)
        (coe MAlonzo.Code.Haskell.Prim.Int.d_ltInt_66)
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.Bounded.du_iBounded_48
        (coe MAlonzo.Code.Haskell.Prim.Bounded.d_iBoundedBelowInt_56)
        (coe MAlonzo.Code.Haskell.Prim.Bounded.d_iBoundedAboveInt_58)
    )

-- Haskell.Prim.Enum.iEnumWord
d_iEnumWord_356 :: T_Enum_24
d_iEnumWord_356 =
  coe
    du_boundedEnumViaInteger_328
    (coe MAlonzo.Code.Haskell.Prim.Word.d_wordToInteger_58)
    (coe MAlonzo.Code.Haskell.Prim.Word.d_integerToWord_52)
    ( coe
        MAlonzo.Code.Haskell.Prim.Ord.du_ordFromLessThan_130
        (coe MAlonzo.Code.Haskell.Prim.Eq.d_iEqWord_34)
        (coe MAlonzo.Code.Haskell.Prim.Word.d_ltWord_42)
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.Bounded.du_iBounded_48
        (coe MAlonzo.Code.Haskell.Prim.Bounded.d_iBoundedBelowWord_52)
        (coe MAlonzo.Code.Haskell.Prim.Bounded.d_iBoundedAboveWord_54)
    )

-- Haskell.Prim.Enum.iEnumBool
d_iEnumBool_358 :: T_Enum_24
d_iEnumBool_358 =
  coe
    du_boundedEnumViaInteger_328
    ( coe
        ( \v0 ->
            coe
              MAlonzo.Code.Haskell.Prim.du_if_then_else__68
              (coe v0)
              (coe (\v1 -> 1 :: Integer))
              (coe (\v1 -> 0 :: Integer))
        )
    )
    ( coe
        ( \v0 ->
            coe
              MAlonzo.Code.Haskell.Prim.Eq.du__'47''61'__16
              (coe MAlonzo.Code.Haskell.Prim.Eq.d_iEqInteger_30)
              (coe v0)
              (coe (0 :: Integer))
        )
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.Ord.du_ordFromCompare_90
        (coe MAlonzo.Code.Haskell.Prim.Eq.d_iEqBool_38)
        ( coe
            ( \v0 v1 ->
                let v2 = coe MAlonzo.Code.Haskell.Prim.Ord.C_EQ_10
                 in coe
                      ( if coe v0
                          then case coe v1 of
                            MAlonzo.Code.Agda.Builtin.Bool.C_false_8 ->
                              coe MAlonzo.Code.Haskell.Prim.Ord.C_GT_12
                            _ -> coe v2
                          else
                            ( case coe v1 of
                                MAlonzo.Code.Agda.Builtin.Bool.C_true_10 ->
                                  coe MAlonzo.Code.Haskell.Prim.Ord.C_LT_8
                                _ -> coe v2
                            )
                      )
            )
        )
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.Bounded.du_iBounded_48
        (coe MAlonzo.Code.Haskell.Prim.Bounded.d_iBoundedBelowBool_60)
        (coe MAlonzo.Code.Haskell.Prim.Bounded.d_iBoundedAboveBool_62)
    )

-- Haskell.Prim.Enum.iEnumOrdering
d_iEnumOrdering_364 :: T_Enum_24
d_iEnumOrdering_364 =
  coe
    du_boundedEnumViaInteger_328
    ( coe
        ( \v0 ->
            case coe v0 of
              MAlonzo.Code.Haskell.Prim.Ord.C_LT_8 -> coe (0 :: Integer)
              MAlonzo.Code.Haskell.Prim.Ord.C_EQ_10 -> coe (1 :: Integer)
              MAlonzo.Code.Haskell.Prim.Ord.C_GT_12 -> coe (2 :: Integer)
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )
    ( coe
        ( \v0 ->
            let v1 = coe MAlonzo.Code.Haskell.Prim.Ord.C_GT_12
             in coe
                  ( case coe v0 of
                      0 -> coe MAlonzo.Code.Haskell.Prim.Ord.C_LT_8
                      1 -> coe MAlonzo.Code.Haskell.Prim.Ord.C_EQ_10
                      _ | coe geqInt (coe v0) (coe (1 :: Integer)) -> coe v1
                      _ -> coe v1
                  )
        )
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.Ord.du_ordFromCompare_90
        (coe MAlonzo.Code.Haskell.Prim.Ord.d_iEqOrdering_14)
        ( coe
            ( \v0 v1 ->
                case coe v0 of
                  MAlonzo.Code.Haskell.Prim.Ord.C_LT_8 ->
                    case coe v1 of
                      MAlonzo.Code.Haskell.Prim.Ord.C_LT_8 ->
                        coe MAlonzo.Code.Haskell.Prim.Ord.C_EQ_10
                      _ -> coe v0
                  MAlonzo.Code.Haskell.Prim.Ord.C_EQ_10 ->
                    case coe v1 of
                      MAlonzo.Code.Haskell.Prim.Ord.C_LT_8 ->
                        coe MAlonzo.Code.Haskell.Prim.Ord.C_GT_12
                      MAlonzo.Code.Haskell.Prim.Ord.C_EQ_10 -> coe v1
                      MAlonzo.Code.Haskell.Prim.Ord.C_GT_12 ->
                        coe MAlonzo.Code.Haskell.Prim.Ord.C_LT_8
                      _ -> MAlonzo.RTE.mazUnreachableError
                  MAlonzo.Code.Haskell.Prim.Ord.C_GT_12 ->
                    case coe v1 of
                      MAlonzo.Code.Haskell.Prim.Ord.C_LT_8 -> coe v0
                      MAlonzo.Code.Haskell.Prim.Ord.C_EQ_10 -> coe v0
                      MAlonzo.Code.Haskell.Prim.Ord.C_GT_12 ->
                        coe MAlonzo.Code.Haskell.Prim.Ord.C_EQ_10
                      _ -> MAlonzo.RTE.mazUnreachableError
                  _ -> MAlonzo.RTE.mazUnreachableError
            )
        )
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.Bounded.du_iBounded_48
        (coe MAlonzo.Code.Haskell.Prim.Bounded.d_iBoundedBelowOrdering_80)
        (coe MAlonzo.Code.Haskell.Prim.Bounded.d_iBoundedAboveOrdering_82)
    )

-- Haskell.Prim.Enum.iEnumUnit
d_iEnumUnit_370 :: T_Enum_24
d_iEnumUnit_370 =
  coe
    du_boundedEnumViaInteger_328
    (coe (\v0 -> 0 :: Integer))
    (coe (\v0 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
    ( coe
        MAlonzo.Code.Haskell.Prim.Ord.du_ordFromCompare_90
        (coe MAlonzo.Code.Haskell.Prim.Eq.d_iEqUnit_42)
        (coe (\v0 v1 -> coe MAlonzo.Code.Haskell.Prim.Ord.C_EQ_10))
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.Bounded.C_Bounded'46'constructor_111
        ( coe
            MAlonzo.Code.Haskell.Prim.Bounded.C_BoundedBelow'46'constructor_3
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
        )
        ( coe
            MAlonzo.Code.Haskell.Prim.Bounded.C_BoundedAbove'46'constructor_53
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
        )
    )

-- Haskell.Prim.Enum.iEnumChar
d_iEnumChar_376 :: T_Enum_24
d_iEnumChar_376 =
  coe
    du_boundedEnumViaInteger_328
    ( coe
        MAlonzo.Code.Haskell.Prim.du__'8728'__28
        (coe (\v0 -> v0))
        (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28)
    )
    ( coe
        ( \v0 ->
            let v1 = '_'
             in coe
                  ( case coe v0 of
                      _
                        | coe geqInt (coe v0) (coe (0 :: Integer)) ->
                            coe MAlonzo.Code.Agda.Builtin.Char.d_primNatToChar_30 v0
                      _ -> coe v1
                  )
        )
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.Ord.du_ordFromLessThan_130
        (coe MAlonzo.Code.Haskell.Prim.Eq.d_iEqChar_40)
        ( coe
            ( \v0 v1 ->
                coe
                  MAlonzo.Code.Haskell.Prim.Ord.d__'60'__58
                  MAlonzo.Code.Haskell.Prim.Ord.d_iOrdNat_246
                  (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v0)
                  (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v1)
            )
        )
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.Bounded.du_iBounded_48
        (coe MAlonzo.Code.Haskell.Prim.Bounded.d_iBoundedBelowChar_64)
        (coe MAlonzo.Code.Haskell.Prim.Bounded.d_iBoundedAboveChar_66)
    )
