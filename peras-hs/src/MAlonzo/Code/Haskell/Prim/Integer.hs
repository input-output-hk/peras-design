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

module MAlonzo.Code.Haskell.Prim.Integer where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.FromNat
import qualified MAlonzo.Code.Agda.Builtin.FromNeg
import qualified MAlonzo.Code.Agda.Builtin.Int
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Haskell.Prim
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

-- Haskell.Prim.Integer.negNat
d_negNat_6 :: Integer -> Integer
d_negNat_6 v0 = coe subInt (coe (0 :: Integer)) (coe v0)

-- Haskell.Prim.Integer.iNumberInteger
d_iNumberInteger_10 ::
  MAlonzo.Code.Agda.Builtin.FromNat.T_Number_10
d_iNumberInteger_10 =
  coe
    MAlonzo.Code.Agda.Builtin.FromNat.C_Number'46'constructor_55
    (\v0 v1 -> v0)

-- Haskell.Prim.Integer.iNegativeInteger
d_iNegativeInteger_14 ::
  MAlonzo.Code.Agda.Builtin.FromNeg.T_Negative_10
d_iNegativeInteger_14 =
  coe
    MAlonzo.Code.Agda.Builtin.FromNeg.C_Negative'46'constructor_55
    (\v0 v1 -> d_negNat_6 (coe v0))

-- Haskell.Prim.Integer.subNat
d_subNat_18 :: Integer -> Integer -> Integer
d_subNat_18 v0 v1 =
  coe
    MAlonzo.Code.Haskell.Prim.du_if_then_else__68
    (coe ltInt (coe v0) (coe v1))
    ( coe
        ( \v2 ->
            subInt
              (coe (-1 :: Integer))
              ( coe
                  MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                  v1
                  (addInt (coe (1 :: Integer)) (coe v0))
              )
        )
    )
    (coe (\v2 -> coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0 v1))

-- Haskell.Prim.Integer.negateInteger
d_negateInteger_24 :: Integer -> Integer
d_negateInteger_24 v0 = coe subInt (coe (0 :: Integer)) (coe v0)

-- Haskell.Prim.Integer.addInteger
d_addInteger_30 :: Integer -> Integer -> Integer
d_addInteger_30 v0 v1 =
  case coe v0 of
    _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
      case coe v1 of
        _
          | coe geqInt (coe v1) (coe (0 :: Integer)) ->
              coe addInt (coe v0) (coe v1)
        _ ->
          coe
            d_subNat_18
            (coe v0)
            (coe subInt (coe (0 :: Integer)) (coe v1))
    _ -> case coe v1 of
      _
        | coe geqInt (coe v1) (coe (0 :: Integer)) ->
            coe d_subNat_18 (coe v1) (coe subInt (coe (0 :: Integer)) (coe v0))
      _ -> coe addInt (coe v0) (coe v1)

-- Haskell.Prim.Integer.subInteger
d_subInteger_48 :: Integer -> Integer -> Integer
d_subInteger_48 v0 v1 =
  coe d_addInteger_30 (coe v0) (coe d_negateInteger_24 (coe v1))

-- Haskell.Prim.Integer.mulInteger
d_mulInteger_54 :: Integer -> Integer -> Integer
d_mulInteger_54 v0 v1 =
  case coe v0 of
    _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
      case coe v1 of
        _
          | coe geqInt (coe v1) (coe (0 :: Integer)) ->
              coe mulInt (coe v0) (coe v1)
        _ ->
          coe
            d_negNat_6
            (coe subInt (coe (0 :: Integer)) (coe mulInt (coe v0) (coe v1)))
    _ -> case coe v1 of
      _
        | coe geqInt (coe v1) (coe (0 :: Integer)) ->
            coe
              d_negNat_6
              (coe subInt (coe (0 :: Integer)) (coe mulInt (coe v0) (coe v1)))
      _ -> coe mulInt (coe v0) (coe v1)

-- Haskell.Prim.Integer.absInteger
d_absInteger_72 :: Integer -> Integer
d_absInteger_72 v0 =
  case coe v0 of
    _ | coe geqInt (coe v0) (coe (0 :: Integer)) -> coe v0
    _ -> coe subInt (coe (0 :: Integer)) (coe v0)

-- Haskell.Prim.Integer.signInteger
d_signInteger_78 :: Integer -> Integer
d_signInteger_78 v0 =
  case coe v0 of
    0 -> coe (0 :: Integer)
    _ | coe geqInt (coe v0) (coe (1 :: Integer)) -> coe (1 :: Integer)
    _ -> coe d_negNat_6 (coe (1 :: Integer))

-- Haskell.Prim.Integer.eqInteger
d_eqInteger_80 :: Integer -> Integer -> Bool
d_eqInteger_80 v0 v1 =
  let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
   in coe
        ( case coe v0 of
            _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
              case coe v1 of
                _
                  | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                      coe eqInt (coe v0) (coe v1)
                _ -> coe v2
            _ -> case coe v1 of
              _
                | coe ltInt (coe v1) (coe (0 :: Integer)) ->
                    coe eqInt (coe v0) (coe v1)
              _ -> coe v2
        )

-- Haskell.Prim.Integer.ltInteger
d_ltInteger_90 :: Integer -> Integer -> Bool
d_ltInteger_90 v0 v1 =
  case coe v0 of
    _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
      case coe v1 of
        _
          | coe geqInt (coe v1) (coe (0 :: Integer)) ->
              coe ltInt (coe v0) (coe v1)
        _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
    _ -> case coe v1 of
      _
        | coe geqInt (coe v1) (coe (0 :: Integer)) ->
            coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> coe ltInt (coe v0) (coe v1)

-- Haskell.Prim.Integer.showInteger
d_showInteger_104 ::
  Integer -> [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_showInteger_104 v0 =
  coe
    MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
    (coe MAlonzo.Code.Agda.Builtin.Int.d_primShowInteger_16 v0)

-- Haskell.Prim.Integer.isNegativeInteger
d_isNegativeInteger_108 :: Integer -> Bool
d_isNegativeInteger_108 v0 =
  case coe v0 of
    _
      | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
    _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10

-- Haskell.Prim.Integer.IsNonNegativeInteger
d_IsNonNegativeInteger_110 :: Integer -> ()
d_IsNonNegativeInteger_110 = erased
