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

module MAlonzo.Code.Haskell.Prim.Int where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.FromNat
import qualified MAlonzo.Code.Agda.Builtin.FromNeg
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Haskell.Prim
import qualified MAlonzo.Code.Haskell.Prim.Integer
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

-- Haskell.Prim.Int.Int
d_Int_6 = ()
newtype T_Int_6 = C_int64_8 MAlonzo.RTE.Word64

-- Haskell.Prim.Int.intToWord
d_intToWord_10 :: T_Int_6 -> MAlonzo.RTE.Word64
d_intToWord_10 v0 =
  case coe v0 of
    C_int64_8 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Int.unsafeIntToNat
d_unsafeIntToNat_14 :: T_Int_6 -> Integer
d_unsafeIntToNat_14 v0 =
  coe word64ToNat (coe d_intToWord_10 (coe v0))

-- Haskell.Prim.Int.2⁶⁴
d_2'8310''8308'_18 :: Integer
d_2'8310''8308'_18 = coe (18446744073709551616 :: Integer)

-- Haskell.Prim.Int.2⁶³
d_2'8310''179'_20 :: Integer
d_2'8310''179'_20 = coe (9223372036854775808 :: Integer)

-- Haskell.Prim.Int.maxInt
d_maxInt_22 :: Integer
d_maxInt_22 =
  coe
    MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
    d_2'8310''179'_20
    (1 :: Integer)

-- Haskell.Prim.Int.iNumberInt
d_iNumberInt_24 :: MAlonzo.Code.Agda.Builtin.FromNat.T_Number_10
d_iNumberInt_24 =
  coe
    MAlonzo.Code.Agda.Builtin.FromNat.C_Number'46'constructor_55
    (\v0 v1 -> coe C_int64_8 (coe word64FromNat (coe v0)))

-- Haskell.Prim.Int.iNegativeInt
d_iNegativeInt_30 ::
  MAlonzo.Code.Agda.Builtin.FromNeg.T_Negative_10
d_iNegativeInt_30 =
  coe
    MAlonzo.Code.Agda.Builtin.FromNeg.C_Negative'46'constructor_55
    ( \v0 v1 ->
        coe
          C_int64_8
          ( coe
              word64FromNat
              ( coe
                  MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                  d_2'8310''8308'_18
                  v0
              )
          )
    )

-- Haskell.Prim.Int.isNegativeInt
d_isNegativeInt_36 :: T_Int_6 -> Bool
d_isNegativeInt_36 v0 =
  case coe v0 of
    C_int64_8 v1 ->
      coe ltInt (coe d_maxInt_22) (coe word64ToNat (coe v1))
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Int.eqInt
d_eqInt_40 :: T_Int_6 -> T_Int_6 -> Bool
d_eqInt_40 v0 v1 =
  case coe v0 of
    C_int64_8 v2 ->
      case coe v1 of
        C_int64_8 v3 -> coe eq64 (coe v2) (coe v3)
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Int.negateInt
d_negateInt_46 :: T_Int_6 -> T_Int_6
d_negateInt_46 v0 =
  case coe v0 of
    C_int64_8 v1 ->
      coe
        C_int64_8
        ( coe
            word64FromNat
            ( coe
                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                d_2'8310''8308'_18
                (word64ToNat (coe v1))
            )
        )
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Int.intToInteger
d_intToInteger_50 :: T_Int_6 -> Integer
d_intToInteger_50 v0 =
  coe
    MAlonzo.Code.Haskell.Prim.du_if_then_else__68
    (coe d_isNegativeInt_36 (coe v0))
    ( coe
        ( \v1 ->
            subInt
              (coe (-1 :: Integer))
              ( coe
                  MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                  (d_unsafeIntToNat_14 (coe d_negateInt_46 (coe v0)))
                  (1 :: Integer)
              )
        )
    )
    (coe (\v1 -> d_unsafeIntToNat_14 (coe v0)))

-- Haskell.Prim.Int.integerToInt
d_integerToInt_54 :: Integer -> T_Int_6
d_integerToInt_54 v0 =
  case coe v0 of
    _
      | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe C_int64_8 (coe word64FromNat (coe v0))
    _ ->
      coe
        d_negateInt_46
        ( coe
            C_int64_8
            ( coe
                sub64
                (coe (0 :: MAlonzo.RTE.Word64))
                (coe word64FromNat (coe v0))
            )
        )

-- Haskell.Prim.Int.ltPosInt
d_ltPosInt_60 :: T_Int_6 -> T_Int_6 -> Bool
d_ltPosInt_60 v0 v1 =
  case coe v0 of
    C_int64_8 v2 ->
      case coe v1 of
        C_int64_8 v3 ->
          coe MAlonzo.Code.Haskell.Prim.Word.d_ltWord_42 (coe v2) (coe v3)
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Int.ltInt
d_ltInt_66 :: T_Int_6 -> T_Int_6 -> Bool
d_ltInt_66 v0 v1 =
  let v2 = d_isNegativeInt_36 (coe v0)
   in coe
        ( let v3 = d_isNegativeInt_36 (coe v1)
           in coe
                ( if coe v2
                    then
                      if coe v3
                        then
                          coe
                            d_ltPosInt_60
                            (coe d_negateInt_46 (coe v1))
                            (coe d_negateInt_46 (coe v0))
                        else coe v2
                    else
                      ( if coe v3
                          then coe v2
                          else coe d_ltPosInt_60 (coe v0) (coe v1)
                      )
                )
        )

-- Haskell.Prim.Int.addInt
d_addInt_92 :: T_Int_6 -> T_Int_6 -> T_Int_6
d_addInt_92 v0 v1 =
  case coe v0 of
    C_int64_8 v2 ->
      case coe v1 of
        C_int64_8 v3 ->
          coe
            C_int64_8
            (coe MAlonzo.Code.Haskell.Prim.Word.d_addWord_18 (coe v2) (coe v3))
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Int.subInt
d_subInt_98 :: T_Int_6 -> T_Int_6 -> T_Int_6
d_subInt_98 v0 v1 =
  coe d_addInt_92 (coe v0) (coe d_negateInt_46 (coe v1))

-- Haskell.Prim.Int.mulInt
d_mulInt_104 :: T_Int_6 -> T_Int_6 -> T_Int_6
d_mulInt_104 v0 v1 =
  case coe v0 of
    C_int64_8 v2 ->
      case coe v1 of
        C_int64_8 v3 ->
          coe
            C_int64_8
            (coe MAlonzo.Code.Haskell.Prim.Word.d_mulWord_30 (coe v2) (coe v3))
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Int.absInt
d_absInt_110 :: T_Int_6 -> T_Int_6
d_absInt_110 v0 =
  coe
    MAlonzo.Code.Haskell.Prim.du_if_then_else__68
    (coe d_isNegativeInt_36 (coe v0))
    (coe (\v1 -> d_negateInt_46 (coe v0)))
    (coe (\v1 -> v0))

-- Haskell.Prim.Int.signInt
d_signInt_114 :: T_Int_6 -> T_Int_6
d_signInt_114 v0 =
  coe
    MAlonzo.Code.Haskell.Prim.du_if_then_else__68
    (coe d_isNegativeInt_36 (coe v0))
    ( coe
        ( \v1 ->
            coe
              C_int64_8
              ( coe
                  word64FromNat
                  ( coe
                      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                      d_2'8310''8308'_18
                      (1 :: Integer)
                  )
              )
        )
    )
    ( coe
        ( \v1 ->
            coe
              MAlonzo.Code.Haskell.Prim.du_if_then_else__68
              ( coe
                  d_eqInt_40
                  (coe v0)
                  (coe C_int64_8 (coe (0 :: MAlonzo.RTE.Word64)))
              )
              (coe (\v2 -> coe C_int64_8 (coe (0 :: MAlonzo.RTE.Word64))))
              (coe (\v2 -> coe C_int64_8 (coe (1 :: MAlonzo.RTE.Word64))))
        )
    )

-- Haskell.Prim.Int.showInt
d_showInt_118 ::
  T_Int_6 -> [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_showInt_118 v0 =
  coe
    MAlonzo.Code.Haskell.Prim.Integer.d_showInteger_104
    (coe d_intToInteger_50 (coe v0))

-- Haskell.Prim.Int.IsNonNegativeInt
d_IsNonNegativeInt_122 :: T_Int_6 -> ()
d_IsNonNegativeInt_122 = erased

-- Haskell.Prim.Int.intToNat
d_intToNat_128 :: T_Int_6 -> AgdaAny -> Integer
d_intToNat_128 v0 ~v1 = du_intToNat_128 v0
du_intToNat_128 :: T_Int_6 -> Integer
du_intToNat_128 v0 = coe d_unsafeIntToNat_14 (coe v0)
