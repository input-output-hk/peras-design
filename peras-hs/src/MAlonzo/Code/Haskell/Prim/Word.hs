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

module MAlonzo.Code.Haskell.Prim.Word where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.FromNat
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.String
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

-- Haskell.Prim.Word.2⁶⁴
d_2'8310''8308'_6 :: Integer
d_2'8310''8308'_6 = coe (18446744073709551616 :: Integer)

-- Haskell.Prim.Word.iNumberWord
d_iNumberWord_8 :: MAlonzo.Code.Agda.Builtin.FromNat.T_Number_10
d_iNumberWord_8 =
  coe
    MAlonzo.Code.Agda.Builtin.FromNat.C_Number'46'constructor_55
    (\v0 v1 -> word64FromNat (coe v0))

-- Haskell.Prim.Word.negateWord
d_negateWord_14 :: MAlonzo.RTE.Word64 -> MAlonzo.RTE.Word64
d_negateWord_14 v0 =
  coe
    word64FromNat
    ( coe
        MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
        d_2'8310''8308'_6
        (word64ToNat (coe v0))
    )

-- Haskell.Prim.Word.addWord
d_addWord_18 ::
  MAlonzo.RTE.Word64 -> MAlonzo.RTE.Word64 -> MAlonzo.RTE.Word64
d_addWord_18 v0 v1 = coe add64 (coe v0) (coe v1)

-- Haskell.Prim.Word.subWord
d_subWord_24 ::
  MAlonzo.RTE.Word64 -> MAlonzo.RTE.Word64 -> MAlonzo.RTE.Word64
d_subWord_24 v0 v1 =
  coe d_addWord_18 (coe v0) (coe d_negateWord_14 (coe v1))

-- Haskell.Prim.Word.mulWord
d_mulWord_30 ::
  MAlonzo.RTE.Word64 -> MAlonzo.RTE.Word64 -> MAlonzo.RTE.Word64
d_mulWord_30 v0 v1 = coe mul64 (coe v0) (coe v1)

-- Haskell.Prim.Word.eqWord
d_eqWord_36 :: MAlonzo.RTE.Word64 -> MAlonzo.RTE.Word64 -> Bool
d_eqWord_36 v0 v1 = coe eq64 (coe v0) (coe v1)

-- Haskell.Prim.Word.ltWord
d_ltWord_42 :: MAlonzo.RTE.Word64 -> MAlonzo.RTE.Word64 -> Bool
d_ltWord_42 v0 v1 = coe lt64 (coe v0) (coe v1)

-- Haskell.Prim.Word.showWord
d_showWord_48 ::
  MAlonzo.RTE.Word64 -> [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_showWord_48 v0 =
  coe
    MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
    ( coe
        MAlonzo.Code.Agda.Builtin.String.d_primShowNat_24
        (word64ToNat (coe v0))
    )

-- Haskell.Prim.Word.integerToWord
d_integerToWord_52 :: Integer -> MAlonzo.RTE.Word64
d_integerToWord_52 v0 =
  case coe v0 of
    _
      | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe word64FromNat (coe v0)
    _ ->
      coe
        d_negateWord_14
        ( coe
            sub64
            (coe (0 :: MAlonzo.RTE.Word64))
            (coe word64FromNat (coe v0))
        )

-- Haskell.Prim.Word.wordToInteger
d_wordToInteger_58 :: MAlonzo.RTE.Word64 -> Integer
d_wordToInteger_58 v0 = coe word64ToNat (coe v0)
