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

module MAlonzo.Code.Haskell.Prim.Num where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Float
import qualified MAlonzo.Code.Agda.Builtin.FromNat
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Haskell.Prim
import qualified MAlonzo.Code.Haskell.Prim.Double
import qualified MAlonzo.Code.Haskell.Prim.Int
import qualified MAlonzo.Code.Haskell.Prim.Integer
import qualified MAlonzo.Code.Haskell.Prim.Monoid
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

-- Haskell.Prim.Num.Num
d_Num_8 a0 = ()
data T_Num_8
  = C_Num'46'constructor_1525
      (AgdaAny -> AgdaAny -> AgdaAny)
      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
      (AgdaAny -> AgdaAny -> AgdaAny)
      (AgdaAny -> AgdaAny -> AgdaAny)
      (AgdaAny -> AgdaAny)
      (AgdaAny -> AgdaAny)
      (Integer -> AgdaAny -> AgdaAny)
      MAlonzo.Code.Agda.Builtin.FromNat.T_Number_10
      AgdaAny
      AgdaAny

-- Haskell.Prim.Num.Num._+_
d__'43'__52 :: T_Num_8 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__52 v0 =
  case coe v0 of
    C_Num'46'constructor_1525 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 ->
      coe v4
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Num.Num._-_
d__'45'__58 :: T_Num_8 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d__'45'__58 v0 =
  case coe v0 of
    C_Num'46'constructor_1525 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 ->
      coe v5
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Num.Num._*_
d__'42'__60 :: T_Num_8 -> AgdaAny -> AgdaAny -> AgdaAny
d__'42'__60 v0 =
  case coe v0 of
    C_Num'46'constructor_1525 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 ->
      coe v6
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Num.Num.negate
d_negate_64 :: T_Num_8 -> AgdaAny -> AgdaAny -> AgdaAny
d_negate_64 v0 =
  case coe v0 of
    C_Num'46'constructor_1525 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 ->
      coe v7
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Num.Num.abs
d_abs_66 :: T_Num_8 -> AgdaAny -> AgdaAny
d_abs_66 v0 =
  case coe v0 of
    C_Num'46'constructor_1525 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 ->
      coe v8
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Num.Num.signum
d_signum_68 :: T_Num_8 -> AgdaAny -> AgdaAny
d_signum_68 v0 =
  case coe v0 of
    C_Num'46'constructor_1525 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 ->
      coe v9
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Num.Num.fromInteger
d_fromInteger_72 :: T_Num_8 -> Integer -> AgdaAny -> AgdaAny
d_fromInteger_72 v0 =
  case coe v0 of
    C_Num'46'constructor_1525 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 ->
      coe v10
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Num.Num.number
d_number_74 ::
  T_Num_8 -> MAlonzo.Code.Agda.Builtin.FromNat.T_Number_10
d_number_74 v0 =
  case coe v0 of
    C_Num'46'constructor_1525 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 ->
      coe v11
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Num.Num.numZero
d_numZero_76 :: T_Num_8 -> AgdaAny
d_numZero_76 v0 =
  case coe v0 of
    C_Num'46'constructor_1525 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 ->
      coe v12
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Num.Num.numOne
d_numOne_78 :: T_Num_8 -> AgdaAny
d_numOne_78 v0 =
  case coe v0 of
    C_Num'46'constructor_1525 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 ->
      coe v13
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Num._._*_
d__'42'__82 :: T_Num_8 -> AgdaAny -> AgdaAny -> AgdaAny
d__'42'__82 v0 = coe d__'42'__60 (coe v0)

-- Haskell.Prim.Num._._+_
d__'43'__84 :: T_Num_8 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__84 v0 = coe d__'43'__52 (coe v0)

-- Haskell.Prim.Num._._-_
d__'45'__86 :: T_Num_8 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d__'45'__86 v0 = coe d__'45'__58 (coe v0)

-- Haskell.Prim.Num._.abs
d_abs_92 :: T_Num_8 -> AgdaAny -> AgdaAny
d_abs_92 v0 = coe d_abs_66 (coe v0)

-- Haskell.Prim.Num._.fromInteger
d_fromInteger_94 :: T_Num_8 -> Integer -> AgdaAny -> AgdaAny
d_fromInteger_94 v0 = coe d_fromInteger_72 (coe v0)

-- Haskell.Prim.Num._.negate
d_negate_96 :: T_Num_8 -> AgdaAny -> AgdaAny -> AgdaAny
d_negate_96 v0 = coe d_negate_64 (coe v0)

-- Haskell.Prim.Num._.numOne
d_numOne_98 :: T_Num_8 -> AgdaAny
d_numOne_98 v0 = coe d_numOne_78 (coe v0)

-- Haskell.Prim.Num._.numZero
d_numZero_100 :: T_Num_8 -> AgdaAny
d_numZero_100 v0 = coe d_numZero_76 (coe v0)

-- Haskell.Prim.Num._.signum
d_signum_102 :: T_Num_8 -> AgdaAny -> AgdaAny
d_signum_102 v0 = coe d_signum_68 (coe v0)

-- Haskell.Prim.Num.iNumNat
d_iNumNat_104 :: T_Num_8
d_iNumNat_104 =
  coe
    C_Num'46'constructor_1525
    (\v0 v1 -> addInt (coe v0) (coe v1))
    (\v0 v1 v2 -> coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0 v1)
    (\v0 v1 -> mulInt (coe v0) (coe v1))
    (\v0 v1 -> v0)
    (\v0 -> v0)
    ( \v0 ->
        case coe v0 of
          0 -> coe (0 :: Integer)
          _ -> coe (1 :: Integer)
    )
    ( \v0 ->
        case coe v0 of
          _ | coe geqInt (coe v0) (coe (0 :: Integer)) -> coe (\v1 -> v0)
          _ -> coe (\v1 -> MAlonzo.RTE.mazUnreachableError)
    )
    MAlonzo.Code.Haskell.Prim.d_iNumberNat_82
    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)

-- Haskell.Prim.Num.iNumInt
d_iNumInt_130 :: T_Num_8
d_iNumInt_130 =
  coe
    C_Num'46'constructor_1525
    ( \v0 v1 ->
        MAlonzo.Code.Haskell.Prim.Int.d_addInt_92 (coe v0) (coe v1)
    )
    ( \v0 v1 v2 ->
        MAlonzo.Code.Haskell.Prim.Int.d_subInt_98 (coe v0) (coe v1)
    )
    ( \v0 v1 ->
        MAlonzo.Code.Haskell.Prim.Int.d_mulInt_104 (coe v0) (coe v1)
    )
    (\v0 v1 -> MAlonzo.Code.Haskell.Prim.Int.d_negateInt_46 (coe v0))
    (\v0 -> MAlonzo.Code.Haskell.Prim.Int.d_absInt_110 (coe v0))
    (\v0 -> MAlonzo.Code.Haskell.Prim.Int.d_signInt_114 (coe v0))
    ( \v0 v1 ->
        MAlonzo.Code.Haskell.Prim.Int.d_integerToInt_54 (coe v0)
    )
    MAlonzo.Code.Haskell.Prim.Int.d_iNumberInt_24
    erased
    erased

-- Haskell.Prim.Num.iNumInteger
d_iNumInteger_152 :: T_Num_8
d_iNumInteger_152 =
  coe
    C_Num'46'constructor_1525
    ( \v0 v1 ->
        MAlonzo.Code.Haskell.Prim.Integer.d_addInteger_30
          (coe v0)
          (coe v1)
    )
    ( \v0 v1 v2 ->
        MAlonzo.Code.Haskell.Prim.Integer.d_subInteger_48
          (coe v0)
          (coe v1)
    )
    ( \v0 v1 ->
        MAlonzo.Code.Haskell.Prim.Integer.d_mulInteger_54
          (coe v0)
          (coe v1)
    )
    ( \v0 v1 ->
        MAlonzo.Code.Haskell.Prim.Integer.d_negateInteger_24 (coe v0)
    )
    ( \v0 ->
        MAlonzo.Code.Haskell.Prim.Integer.d_absInteger_72 (coe v0)
    )
    ( \v0 ->
        MAlonzo.Code.Haskell.Prim.Integer.d_signInteger_78 (coe v0)
    )
    (\v0 v1 -> v0)
    MAlonzo.Code.Haskell.Prim.Integer.d_iNumberInteger_10
    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)

-- Haskell.Prim.Num.iNumWord
d_iNumWord_174 :: T_Num_8
d_iNumWord_174 =
  coe
    C_Num'46'constructor_1525
    ( \v0 v1 ->
        MAlonzo.Code.Haskell.Prim.Word.d_addWord_18 (coe v0) (coe v1)
    )
    ( \v0 v1 v2 ->
        MAlonzo.Code.Haskell.Prim.Word.d_subWord_24 (coe v0) (coe v1)
    )
    ( \v0 v1 ->
        MAlonzo.Code.Haskell.Prim.Word.d_mulWord_30 (coe v0) (coe v1)
    )
    ( \v0 v1 ->
        MAlonzo.Code.Haskell.Prim.Word.d_negateWord_14 (coe v0)
    )
    (\v0 -> v0)
    ( \v0 ->
        coe
          MAlonzo.Code.Haskell.Prim.du_if_then_else__68
          ( coe
              MAlonzo.Code.Haskell.Prim.Word.d_eqWord_36
              (coe v0)
              (coe (0 :: MAlonzo.RTE.Word64))
          )
          (coe (\v1 -> 0 :: MAlonzo.RTE.Word64))
          (coe (\v1 -> 1 :: MAlonzo.RTE.Word64))
    )
    ( \v0 v1 ->
        MAlonzo.Code.Haskell.Prim.Word.d_integerToWord_52 (coe v0)
    )
    MAlonzo.Code.Haskell.Prim.Word.d_iNumberWord_8
    erased
    erased

-- Haskell.Prim.Num.iNumDouble
d_iNumDouble_196 :: T_Num_8
d_iNumDouble_196 =
  coe
    C_Num'46'constructor_1525
    ( \v0 v1 ->
        coe MAlonzo.Code.Agda.Builtin.Float.d_primFloatPlus_48 v0 v1
    )
    ( \v0 v1 v2 ->
        coe MAlonzo.Code.Agda.Builtin.Float.d_primFloatMinus_50 v0 v1
    )
    ( \v0 v1 ->
        coe MAlonzo.Code.Agda.Builtin.Float.d_primFloatTimes_52 v0 v1
    )
    ( \v0 v1 ->
        coe
          MAlonzo.Code.Agda.Builtin.Float.d_primFloatMinus_50
          (0.0 :: Double)
          v0
    )
    ( \v0 ->
        coe
          MAlonzo.Code.Haskell.Prim.du_if_then_else__68
          ( coe
              MAlonzo.Code.Agda.Builtin.Float.d_primFloatLess_12
              v0
              (0.0 :: Double)
          )
          ( coe
              ( \v1 ->
                  coe
                    MAlonzo.Code.Agda.Builtin.Float.d_primFloatMinus_50
                    (0.0 :: Double)
                    v0
              )
          )
          (coe (\v1 -> v0))
    )
    ( \v0 ->
        coe
          MAlonzo.Code.Haskell.Prim.du_case_of__58
          ( coe
              MAlonzo.Code.Haskell.Prim.du_if_then_else__68
              ( coe
                  MAlonzo.Code.Agda.Builtin.Float.d_primFloatLess_12
                  v0
                  (0.0 :: Double)
              )
              (coe (\v1 -> coe MAlonzo.Code.Haskell.Prim.Ord.C_LT_8))
              ( coe
                  ( \v1 ->
                      coe
                        MAlonzo.Code.Haskell.Prim.du_if_then_else__68
                        ( coe
                            MAlonzo.Code.Agda.Builtin.Float.d_primFloatEquality_10
                            v0
                            (0.0 :: Double)
                        )
                        (coe (\v2 -> coe MAlonzo.Code.Haskell.Prim.Ord.C_EQ_10))
                        (coe (\v2 -> coe MAlonzo.Code.Haskell.Prim.Ord.C_GT_12))
                  )
              )
          )
          ( coe
              ( \v1 v2 ->
                  case coe v1 of
                    MAlonzo.Code.Haskell.Prim.Ord.C_LT_8 -> coe (-1.0 :: Double)
                    MAlonzo.Code.Haskell.Prim.Ord.C_EQ_10 -> coe v0
                    MAlonzo.Code.Haskell.Prim.Ord.C_GT_12 -> coe (1.0 :: Double)
                    _ -> MAlonzo.RTE.mazUnreachableError
              )
          )
    )
    ( \v0 ->
        case coe v0 of
          _
            | coe geqInt (coe v0) (coe (0 :: Integer)) ->
                coe
                  ( \v1 ->
                      coe MAlonzo.Code.Agda.Builtin.Float.d_primNatToFloat_24 v0
                  )
          _ ->
            coe
              ( \v1 ->
                  coe
                    MAlonzo.Code.Agda.Builtin.Float.d_primFloatMinus_50
                    (0.0 :: Double)
                    ( coe
                        MAlonzo.Code.Agda.Builtin.Float.d_primNatToFloat_24
                        (subInt (coe (0 :: Integer)) (coe v0))
                    )
              )
    )
    MAlonzo.Code.Haskell.Prim.Double.d_iNumberDouble_6
    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)

-- Haskell.Prim.Num.MonoidSum
d_MonoidSum_224 ::
  () -> T_Num_8 -> MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74
d_MonoidSum_224 ~v0 v1 = du_MonoidSum_224 v1
du_MonoidSum_224 ::
  T_Num_8 -> MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74
du_MonoidSum_224 v0 =
  coe
    MAlonzo.Code.Haskell.Prim.Monoid.C_Monoid'46'constructor_4387
    ( coe
        MAlonzo.Code.Agda.Builtin.FromNat.d_fromNat_30
        (d_number_74 (coe v0))
        (0 :: Integer)
        (d_numZero_76 (coe v0))
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.Monoid.d_super_106
        ( coe
            MAlonzo.Code.Haskell.Prim.Monoid.C_DefaultMonoid'46'constructor_4503
            ( coe
                MAlonzo.Code.Agda.Builtin.FromNat.d_fromNat_30
                (d_number_74 (coe v0))
                (0 :: Integer)
                (d_numZero_76 (coe v0))
            )
            ( coe
                MAlonzo.Code.Haskell.Prim.Monoid.C_Semigroup'46'constructor_7
                (coe d__'43'__52 (coe v0))
            )
        )
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.Monoid.du_mappend_108
        ( coe
            MAlonzo.Code.Haskell.Prim.Monoid.C_DefaultMonoid'46'constructor_4503
            ( coe
                MAlonzo.Code.Agda.Builtin.FromNat.d_fromNat_30
                (d_number_74 (coe v0))
                (0 :: Integer)
                (d_numZero_76 (coe v0))
            )
            ( coe
                MAlonzo.Code.Haskell.Prim.Monoid.C_Semigroup'46'constructor_7
                (coe d__'43'__52 (coe v0))
            )
        )
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.Monoid.du_mconcat_110
        ( coe
            MAlonzo.Code.Haskell.Prim.Monoid.C_DefaultMonoid'46'constructor_4503
            ( coe
                MAlonzo.Code.Agda.Builtin.FromNat.d_fromNat_30
                (d_number_74 (coe v0))
                (0 :: Integer)
                (d_numZero_76 (coe v0))
            )
            ( coe
                MAlonzo.Code.Haskell.Prim.Monoid.C_Semigroup'46'constructor_7
                (coe d__'43'__52 (coe v0))
            )
        )
    )

-- Haskell.Prim.Num.MonoidProduct
d_MonoidProduct_242 ::
  () -> T_Num_8 -> MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74
d_MonoidProduct_242 ~v0 v1 = du_MonoidProduct_242 v1
du_MonoidProduct_242 ::
  T_Num_8 -> MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74
du_MonoidProduct_242 v0 =
  coe
    MAlonzo.Code.Haskell.Prim.Monoid.C_Monoid'46'constructor_4387
    ( coe
        MAlonzo.Code.Agda.Builtin.FromNat.d_fromNat_30
        (d_number_74 (coe v0))
        (1 :: Integer)
        (d_numOne_78 (coe v0))
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.Monoid.d_super_106
        ( coe
            MAlonzo.Code.Haskell.Prim.Monoid.C_DefaultMonoid'46'constructor_4503
            ( coe
                MAlonzo.Code.Agda.Builtin.FromNat.d_fromNat_30
                (d_number_74 (coe v0))
                (1 :: Integer)
                (d_numOne_78 (coe v0))
            )
            ( coe
                MAlonzo.Code.Haskell.Prim.Monoid.C_Semigroup'46'constructor_7
                (coe d__'42'__60 (coe v0))
            )
        )
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.Monoid.du_mappend_108
        ( coe
            MAlonzo.Code.Haskell.Prim.Monoid.C_DefaultMonoid'46'constructor_4503
            ( coe
                MAlonzo.Code.Agda.Builtin.FromNat.d_fromNat_30
                (d_number_74 (coe v0))
                (1 :: Integer)
                (d_numOne_78 (coe v0))
            )
            ( coe
                MAlonzo.Code.Haskell.Prim.Monoid.C_Semigroup'46'constructor_7
                (coe d__'42'__60 (coe v0))
            )
        )
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.Monoid.du_mconcat_110
        ( coe
            MAlonzo.Code.Haskell.Prim.Monoid.C_DefaultMonoid'46'constructor_4503
            ( coe
                MAlonzo.Code.Agda.Builtin.FromNat.d_fromNat_30
                (d_number_74 (coe v0))
                (1 :: Integer)
                (d_numOne_78 (coe v0))
            )
            ( coe
                MAlonzo.Code.Haskell.Prim.Monoid.C_Semigroup'46'constructor_7
                (coe d__'42'__60 (coe v0))
            )
        )
    )
