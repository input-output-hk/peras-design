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

module MAlonzo.Code.Haskell.Prim.String where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.FromString
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Haskell.Prim
import qualified MAlonzo.Code.Haskell.Prim.Foldable
import qualified MAlonzo.Code.Haskell.Prim.List
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

-- Haskell.Prim.String.String
d_String_6 :: ()
d_String_6 = erased

-- Haskell.Prim.String.iIsStringString
d_iIsStringString_8 ::
  MAlonzo.Code.Agda.Builtin.FromString.T_IsString_10
d_iIsStringString_8 =
  coe
    MAlonzo.Code.Agda.Builtin.FromString.C_IsString'46'constructor_37
    ( \v0 v1 ->
        coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0
    )

-- Haskell.Prim.String.cons
d_cons_12 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]] ->
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]]
d_cons_12 v0 v1 =
  case coe v1 of
    [] ->
      coe
        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
        ( coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe v0)
            (coe v1)
        )
        (coe v1)
    (:) v2 v3 ->
      coe
        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
        ( coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe v0)
            (coe v2)
        )
        (coe v3)
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.String.lines
d_lines_22 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]]
d_lines_22 v0 =
  case coe v0 of
    [] -> coe v0
    (:) v1 v2 ->
      let v3 = d_cons_12 (coe v1) (coe d_lines_22 (coe v2))
       in coe
            ( case coe v1 of
                '\n' ->
                  coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                    (coe d_lines_22 (coe v2))
                _ -> coe v3
            )
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.String.space
d_space_30 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]]
d_space_30 v0 =
  case coe v0 of
    [] -> coe v0
    (:) v1 v2 ->
      coe
        MAlonzo.Code.Haskell.Prim.du_if_then_else__68
        (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsSpace_14 v1)
        (coe (\v3 -> d_space_30 (coe v2)))
        (coe (\v3 -> d_cons_12 (coe v1) (coe d_word_32 (coe v2))))
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.String.word
d_word_32 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]]
d_word_32 v0 =
  case coe v0 of
    [] -> coe v0
    (:) v1 v2 ->
      coe
        MAlonzo.Code.Haskell.Prim.du_if_then_else__68
        (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsSpace_14 v1)
        ( coe
            ( \v3 ->
                coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                  (coe d_space_30 (coe v2))
            )
        )
        (coe (\v3 -> d_cons_12 (coe v1) (coe d_word_32 (coe v2))))
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.String.words
d_words_42 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]]
d_words_42 v0 =
  case coe v0 of
    [] -> coe v0
    (:) v1 v2 ->
      coe
        MAlonzo.Code.Haskell.Prim.du_if_then_else__68
        (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsSpace_14 v1)
        (coe (\v3 -> d_space_30 (coe v2)))
        (coe (\v3 -> d_word_32 (coe v0)))
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.String.unlines
d_unlines_50 ::
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_unlines_50 =
  coe
    MAlonzo.Code.Haskell.Prim.Foldable.du_concatMap_190
    ( coe
        MAlonzo.Code.Haskell.Prim.Foldable.C_DefaultFoldable'46'constructor_4805
        ( \v0 v1 v2 v3 v4 ->
            coe
              MAlonzo.Code.Haskell.Prim.Foldable.du_foldMapList_408
              v2
              v3
              v4
        )
    )
    ( \v0 ->
        coe
          MAlonzo.Code.Haskell.Prim.List.du__'43''43'__20
          (coe v0)
          ( coe
              MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
              ("\n" :: Data.Text.Text)
          )
    )

-- Haskell.Prim.String.unwords
d_unwords_54 ::
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_unwords_54 v0 =
  case coe v0 of
    [] ->
      coe
        MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
        ("" :: Data.Text.Text)
    (:) v1 v2 ->
      let v3 =
            coe
              MAlonzo.Code.Haskell.Prim.List.du__'43''43'__20
              (coe v1)
              ( coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe ' ')
                  (coe d_unwords_54 (coe v2))
              )
       in coe
            ( case coe v2 of
                [] -> coe v1
                _ -> coe v3
            )
    _ -> MAlonzo.RTE.mazUnreachableError
