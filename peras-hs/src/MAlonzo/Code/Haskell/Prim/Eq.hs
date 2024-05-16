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

module MAlonzo.Code.Haskell.Prim.Eq where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Float
import qualified MAlonzo.Code.Haskell.Prim.Bool
import qualified MAlonzo.Code.Haskell.Prim.Either
import qualified MAlonzo.Code.Haskell.Prim.Int
import qualified MAlonzo.Code.Haskell.Prim.Integer
import qualified MAlonzo.Code.Haskell.Prim.Maybe
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

-- Haskell.Prim.Eq.Eq
d_Eq_8 a0 = ()
newtype T_Eq_8 = C_Eq'46'constructor_7 (AgdaAny -> AgdaAny -> Bool)

-- Haskell.Prim.Eq.Eq._==_
d__'61''61'__14 :: T_Eq_8 -> AgdaAny -> AgdaAny -> Bool
d__'61''61'__14 v0 =
  case coe v0 of
    C_Eq'46'constructor_7 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Eq.Eq._/=_
d__'47''61'__16 :: () -> T_Eq_8 -> AgdaAny -> AgdaAny -> Bool
d__'47''61'__16 ~v0 v1 v2 v3 = du__'47''61'__16 v1 v2 v3
du__'47''61'__16 :: T_Eq_8 -> AgdaAny -> AgdaAny -> Bool
du__'47''61'__16 v0 v1 v2 =
  coe
    MAlonzo.Code.Haskell.Prim.Bool.d_not_14
    (coe d__'61''61'__14 v0 v1 v2)

-- Haskell.Prim.Eq._._/=_
d__'47''61'__24 :: () -> T_Eq_8 -> AgdaAny -> AgdaAny -> Bool
d__'47''61'__24 ~v0 v1 = du__'47''61'__24 v1
du__'47''61'__24 :: T_Eq_8 -> AgdaAny -> AgdaAny -> Bool
du__'47''61'__24 v0 = coe du__'47''61'__16 (coe v0)

-- Haskell.Prim.Eq._._==_
d__'61''61'__26 :: T_Eq_8 -> AgdaAny -> AgdaAny -> Bool
d__'61''61'__26 v0 = coe d__'61''61'__14 (coe v0)

-- Haskell.Prim.Eq.iEqNat
d_iEqNat_28 :: T_Eq_8
d_iEqNat_28 = coe C_Eq'46'constructor_7 (coe eqInt)

-- Haskell.Prim.Eq.iEqInteger
d_iEqInteger_30 :: T_Eq_8
d_iEqInteger_30 =
  coe
    C_Eq'46'constructor_7
    (coe MAlonzo.Code.Haskell.Prim.Integer.d_eqInteger_80)

-- Haskell.Prim.Eq.iEqInt
d_iEqInt_32 :: T_Eq_8
d_iEqInt_32 =
  coe
    C_Eq'46'constructor_7
    (coe MAlonzo.Code.Haskell.Prim.Int.d_eqInt_40)

-- Haskell.Prim.Eq.iEqWord
d_iEqWord_34 :: T_Eq_8
d_iEqWord_34 =
  coe
    C_Eq'46'constructor_7
    (coe MAlonzo.Code.Haskell.Prim.Word.d_eqWord_36)

-- Haskell.Prim.Eq.iEqDouble
d_iEqDouble_36 :: T_Eq_8
d_iEqDouble_36 =
  coe
    C_Eq'46'constructor_7
    (coe MAlonzo.Code.Agda.Builtin.Float.d_primFloatEquality_10)

-- Haskell.Prim.Eq.iEqBool
d_iEqBool_38 :: T_Eq_8
d_iEqBool_38 =
  coe
    C_Eq'46'constructor_7
    ( coe
        ( \v0 ->
            if coe v0
              then
                coe
                  ( \v1 ->
                      let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                       in coe
                            ( case coe v1 of
                                MAlonzo.Code.Agda.Builtin.Bool.C_true_10 -> coe v1
                                _ -> coe v2
                            )
                  )
              else
                coe
                  ( \v1 ->
                      case coe v1 of
                        MAlonzo.Code.Agda.Builtin.Bool.C_false_8 ->
                          coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                        _ -> coe v0
                  )
        )
    )

-- Haskell.Prim.Eq.iEqChar
d_iEqChar_40 :: T_Eq_8
d_iEqChar_40 =
  coe
    C_Eq'46'constructor_7
    (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharEquality_32)

-- Haskell.Prim.Eq.iEqUnit
d_iEqUnit_42 :: T_Eq_8
d_iEqUnit_42 =
  coe
    C_Eq'46'constructor_7
    (coe (\v0 v1 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))

-- Haskell.Prim.Eq.iEqTuple₂
d_iEqTuple'8322'_44 :: () -> () -> T_Eq_8 -> T_Eq_8 -> T_Eq_8
d_iEqTuple'8322'_44 ~v0 ~v1 v2 v3 = du_iEqTuple'8322'_44 v2 v3
du_iEqTuple'8322'_44 :: T_Eq_8 -> T_Eq_8 -> T_Eq_8
du_iEqTuple'8322'_44 v0 v1 =
  coe
    C_Eq'46'constructor_7
    ( coe
        ( \v2 ->
            case coe v2 of
              MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24 v3 v4 ->
                coe
                  ( \v5 ->
                      case coe v5 of
                        MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24 v6 v7 ->
                          coe
                            MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                            (coe d__'61''61'__14 v0 v3 v6)
                            (coe d__'61''61'__14 v1 v7 v7)
                        _ -> MAlonzo.RTE.mazUnreachableError
                  )
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )

-- Haskell.Prim.Eq.iEqTuple₃
d_iEqTuple'8323'_54 ::
  () -> () -> () -> T_Eq_8 -> T_Eq_8 -> T_Eq_8 -> T_Eq_8
d_iEqTuple'8323'_54 ~v0 ~v1 ~v2 v3 v4 v5 =
  du_iEqTuple'8323'_54 v3 v4 v5
du_iEqTuple'8323'_54 :: T_Eq_8 -> T_Eq_8 -> T_Eq_8 -> T_Eq_8
du_iEqTuple'8323'_54 v0 v1 v2 =
  coe
    C_Eq'46'constructor_7
    ( coe
        ( \v3 ->
            case coe v3 of
              MAlonzo.Code.Haskell.Prim.Tuple.C__'44'_'44'__40 v4 v5 v6 ->
                coe
                  ( \v7 ->
                      case coe v7 of
                        MAlonzo.Code.Haskell.Prim.Tuple.C__'44'_'44'__40 v8 v9 v10 ->
                          coe
                            MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                            (coe d__'61''61'__14 v0 v4 v8)
                            ( coe
                                MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                                (coe d__'61''61'__14 v1 v9 v9)
                                (coe d__'61''61'__14 v2 v6 v10)
                            )
                        _ -> MAlonzo.RTE.mazUnreachableError
                  )
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )

-- Haskell.Prim.Eq.iEqList
d_iEqList_68 :: () -> T_Eq_8 -> T_Eq_8
d_iEqList_68 ~v0 v1 = du_iEqList_68 v1
du_iEqList_68 :: T_Eq_8 -> T_Eq_8
du_iEqList_68 v0 =
  coe C_Eq'46'constructor_7 (coe du_eqList_76 (coe v0))

-- Haskell.Prim.Eq._.eqList
d_eqList_76 :: () -> T_Eq_8 -> [AgdaAny] -> [AgdaAny] -> Bool
d_eqList_76 ~v0 v1 v2 v3 = du_eqList_76 v1 v2 v3
du_eqList_76 :: T_Eq_8 -> [AgdaAny] -> [AgdaAny] -> Bool
du_eqList_76 v0 v1 v2 =
  let v3 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
   in coe
        ( case coe v1 of
            [] ->
              case coe v2 of
                [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v3
            (:) v4 v5 ->
              case coe v2 of
                (:) v6 v7 ->
                  coe
                    MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                    (coe d__'61''61'__14 v0 v4 v6)
                    (coe du_eqList_76 (coe v0) (coe v5) (coe v7))
                _ -> coe v3
            _ -> MAlonzo.RTE.mazUnreachableError
        )

-- Haskell.Prim.Eq.iEqMaybe
d_iEqMaybe_86 :: () -> T_Eq_8 -> T_Eq_8
d_iEqMaybe_86 ~v0 v1 = du_iEqMaybe_86 v1
du_iEqMaybe_86 :: T_Eq_8 -> T_Eq_8
du_iEqMaybe_86 v0 =
  coe
    C_Eq'46'constructor_7
    ( coe
        ( \v1 ->
            case coe v1 of
              MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16 ->
                coe
                  ( \v2 ->
                      let v3 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                       in coe
                            ( case coe v2 of
                                MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16 ->
                                  coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                _ -> coe v3
                            )
                  )
              MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 v2 ->
                coe
                  ( \v3 ->
                      let v4 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                       in coe
                            ( case coe v3 of
                                MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 v5 ->
                                  coe d__'61''61'__14 v0 v2 v5
                                _ -> coe v4
                            )
                  )
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )

-- Haskell.Prim.Eq.iEqEither
d_iEqEither_92 :: () -> () -> T_Eq_8 -> T_Eq_8 -> T_Eq_8
d_iEqEither_92 ~v0 ~v1 v2 v3 = du_iEqEither_92 v2 v3
du_iEqEither_92 :: T_Eq_8 -> T_Eq_8 -> T_Eq_8
du_iEqEither_92 v0 v1 =
  coe
    C_Eq'46'constructor_7
    ( coe
        ( \v2 ->
            case coe v2 of
              MAlonzo.Code.Haskell.Prim.Either.C_Left_16 v3 ->
                coe
                  ( \v4 ->
                      let v5 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                       in coe
                            ( case coe v4 of
                                MAlonzo.Code.Haskell.Prim.Either.C_Left_16 v6 ->
                                  coe d__'61''61'__14 v0 v3 v6
                                _ -> coe v5
                            )
                  )
              MAlonzo.Code.Haskell.Prim.Either.C_Right_18 v3 ->
                coe
                  ( \v4 ->
                      let v5 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                       in coe
                            ( case coe v4 of
                                MAlonzo.Code.Haskell.Prim.Either.C_Right_18 v6 ->
                                  coe d__'61''61'__14 v1 v3 v6
                                _ -> coe v5
                            )
                  )
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )
