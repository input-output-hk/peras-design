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

module MAlonzo.Code.Haskell.Prim.List where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Haskell.Prim
import qualified MAlonzo.Code.Haskell.Prim.Bool
import qualified MAlonzo.Code.Haskell.Prim.Int
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

-- Haskell.Prim.List.map
d_map_6 ::
  () -> () -> (AgdaAny -> AgdaAny) -> [AgdaAny] -> [AgdaAny]
d_map_6 ~v0 ~v1 v2 v3 = du_map_6 v2 v3
du_map_6 :: (AgdaAny -> AgdaAny) -> [AgdaAny] -> [AgdaAny]
du_map_6 v0 v1 =
  case coe v1 of
    [] -> coe v1
    (:) v2 v3 ->
      coe
        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
        (coe v0 v2)
        (coe du_map_6 (coe v0) (coe v3))
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.List._++_
d__'43''43'__20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny]
d__'43''43'__20 ~v0 ~v1 v2 v3 = du__'43''43'__20 v2 v3
du__'43''43'__20 :: [AgdaAny] -> [AgdaAny] -> [AgdaAny]
du__'43''43'__20 v0 v1 =
  case coe v0 of
    [] -> coe v1
    (:) v2 v3 ->
      coe
        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
        (coe v2)
        (coe du__'43''43'__20 (coe v3) (coe v1))
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.List.filter
d_filter_30 :: () -> (AgdaAny -> Bool) -> [AgdaAny] -> [AgdaAny]
d_filter_30 ~v0 v1 v2 = du_filter_30 v1 v2
du_filter_30 :: (AgdaAny -> Bool) -> [AgdaAny] -> [AgdaAny]
du_filter_30 v0 v1 =
  case coe v1 of
    [] -> coe v1
    (:) v2 v3 ->
      coe
        MAlonzo.Code.Haskell.Prim.du_if_then_else__68
        (coe v0 v2)
        ( coe
            ( \v4 ->
                coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe v2)
                  (coe du_filter_30 (coe v0) (coe v3))
            )
        )
        (coe (\v4 -> coe du_filter_30 (coe v0) (coe v3)))
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.List.scanl
d_scanl_40 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny]
d_scanl_40 ~v0 ~v1 v2 v3 v4 = du_scanl_40 v2 v3 v4
du_scanl_40 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny]
du_scanl_40 v0 v1 v2 =
  case coe v2 of
    [] ->
      coe
        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
        (coe v1)
        (coe v2)
    (:) v3 v4 ->
      coe
        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
        (coe v1)
        (coe du_scanl_40 (coe v0) (coe v0 v1 v3) (coe v4))
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.List.scanr
d_scanr_54 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny]
d_scanr_54 ~v0 ~v1 v2 v3 v4 = du_scanr_54 v2 v3 v4
du_scanr_54 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny]
du_scanr_54 v0 v1 v2 =
  case coe v2 of
    [] ->
      coe
        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
        (coe v1)
        (coe v2)
    (:) v3 v4 ->
      coe
        MAlonzo.Code.Haskell.Prim.du_case_of__58
        (coe du_scanr_54 (coe v0) (coe v1) (coe v4))
        ( coe
            ( \v5 v6 ->
                case coe v5 of
                  [] -> coe v5
                  (:) v7 v8 ->
                    coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe v0 v3 v7)
                      (coe v5)
                  _ -> MAlonzo.RTE.mazUnreachableError
            )
        )
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.List.scanl1
d_scanl1_74 ::
  () -> (AgdaAny -> AgdaAny -> AgdaAny) -> [AgdaAny] -> [AgdaAny]
d_scanl1_74 ~v0 v1 v2 = du_scanl1_74 v1 v2
du_scanl1_74 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> [AgdaAny] -> [AgdaAny]
du_scanl1_74 v0 v1 =
  case coe v1 of
    [] -> coe v1
    (:) v2 v3 -> coe du_scanl_40 (coe v0) (coe v2) (coe v3)
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.List.scanr1
d_scanr1_84 ::
  () -> (AgdaAny -> AgdaAny -> AgdaAny) -> [AgdaAny] -> [AgdaAny]
d_scanr1_84 ~v0 v1 v2 = du_scanr1_84 v1 v2
du_scanr1_84 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> [AgdaAny] -> [AgdaAny]
du_scanr1_84 v0 v1 =
  case coe v1 of
    [] -> coe v1
    (:) v2 v3 ->
      let v4 =
            coe
              MAlonzo.Code.Haskell.Prim.du_case_of__58
              (coe du_scanr1_84 (coe v0) (coe v3))
              ( coe
                  ( \v4 v5 ->
                      case coe v4 of
                        [] -> coe v4
                        (:) v6 v7 ->
                          coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe v0 v2 v6)
                            (coe v4)
                        _ -> MAlonzo.RTE.mazUnreachableError
                  )
              )
       in coe
            ( case coe v3 of
                [] -> coe v1
                _ -> coe v4
            )
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.List.takeWhile
d_takeWhile_104 ::
  () -> (AgdaAny -> Bool) -> [AgdaAny] -> [AgdaAny]
d_takeWhile_104 ~v0 v1 v2 = du_takeWhile_104 v1 v2
du_takeWhile_104 :: (AgdaAny -> Bool) -> [AgdaAny] -> [AgdaAny]
du_takeWhile_104 v0 v1 =
  case coe v1 of
    [] -> coe v1
    (:) v2 v3 ->
      coe
        MAlonzo.Code.Haskell.Prim.du_if_then_else__68
        (coe v0 v2)
        ( coe
            ( \v4 ->
                coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe v2)
                  (coe du_takeWhile_104 (coe v0) (coe v3))
            )
        )
        (coe (\v4 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.List.dropWhile
d_dropWhile_114 ::
  () -> (AgdaAny -> Bool) -> [AgdaAny] -> [AgdaAny]
d_dropWhile_114 ~v0 v1 v2 = du_dropWhile_114 v1 v2
du_dropWhile_114 :: (AgdaAny -> Bool) -> [AgdaAny] -> [AgdaAny]
du_dropWhile_114 v0 v1 =
  case coe v1 of
    [] -> coe v1
    (:) v2 v3 ->
      coe
        MAlonzo.Code.Haskell.Prim.du_if_then_else__68
        (coe v0 v2)
        (coe (\v4 -> coe du_dropWhile_114 (coe v0) (coe v3)))
        (coe (\v4 -> v1))
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.List.span
d_span_124 ::
  () ->
  (AgdaAny -> Bool) ->
  [AgdaAny] ->
  MAlonzo.Code.Haskell.Prim.Tuple.T__'215'__10
d_span_124 ~v0 v1 v2 = du_span_124 v1 v2
du_span_124 ::
  (AgdaAny -> Bool) ->
  [AgdaAny] ->
  MAlonzo.Code.Haskell.Prim.Tuple.T__'215'__10
du_span_124 v0 v1 =
  case coe v1 of
    [] ->
      coe
        MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24
        (coe v1)
        (coe v1)
    (:) v2 v3 ->
      coe
        MAlonzo.Code.Haskell.Prim.du_if_then_else__68
        (coe v0 v2)
        ( coe
            ( \v4 ->
                coe
                  MAlonzo.Code.Haskell.Prim.Tuple.du_first_58
                  (coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2))
                  (coe du_span_124 (coe v0) (coe v3))
            )
        )
        ( coe
            ( \v4 ->
                coe
                  MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                  (coe v1)
            )
        )
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.List.break
d_break_136 ::
  () ->
  (AgdaAny -> Bool) ->
  [AgdaAny] ->
  MAlonzo.Code.Haskell.Prim.Tuple.T__'215'__10
d_break_136 ~v0 v1 = du_break_136 v1
du_break_136 ::
  (AgdaAny -> Bool) ->
  [AgdaAny] ->
  MAlonzo.Code.Haskell.Prim.Tuple.T__'215'__10
du_break_136 v0 =
  coe
    du_span_124
    ( coe
        MAlonzo.Code.Haskell.Prim.du__'8728'__28
        (coe MAlonzo.Code.Haskell.Prim.Bool.d_not_14)
        (coe v0)
    )

-- Haskell.Prim.List.zipWith
d_zipWith_140 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny]
d_zipWith_140 ~v0 ~v1 ~v2 v3 v4 v5 = du_zipWith_140 v3 v4 v5
du_zipWith_140 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny]
du_zipWith_140 v0 v1 v2 =
  case coe v1 of
    [] -> coe v1
    (:) v3 v4 ->
      case coe v2 of
        [] -> coe v2
        (:) v5 v6 ->
          coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe v0 v3 v5)
            (coe du_zipWith_140 (coe v0) (coe v4) (coe v6))
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.List.zip
d_zip_156 ::
  () ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [MAlonzo.Code.Haskell.Prim.Tuple.T__'215'__10]
d_zip_156 ~v0 ~v1 = du_zip_156
du_zip_156 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [MAlonzo.Code.Haskell.Prim.Tuple.T__'215'__10]
du_zip_156 =
  coe
    du_zipWith_140
    (coe MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24)

-- Haskell.Prim.List.zipWith3
d_zipWith3_158 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny]
d_zipWith3_158 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 =
  du_zipWith3_158 v4 v5 v6 v7
du_zipWith3_158 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny]
du_zipWith3_158 v0 v1 v2 v3 =
  case coe v1 of
    [] -> coe v1
    (:) v4 v5 ->
      case coe v2 of
        [] -> coe v2
        (:) v6 v7 ->
          case coe v3 of
            [] -> coe v3
            (:) v8 v9 ->
              coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe v0 v4 v6 v8)
                (coe du_zipWith3_158 (coe v0) (coe v5) (coe v7) (coe v9))
            _ -> MAlonzo.RTE.mazUnreachableError
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.List.zip3
d_zip3_180 ::
  () ->
  () ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [MAlonzo.Code.Haskell.Prim.Tuple.T__'215'_'215'__32]
d_zip3_180 ~v0 ~v1 ~v2 = du_zip3_180
du_zip3_180 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [MAlonzo.Code.Haskell.Prim.Tuple.T__'215'_'215'__32]
du_zip3_180 =
  coe
    du_zipWith3_158
    (coe MAlonzo.Code.Haskell.Prim.Tuple.C__'44'_'44'__40)

-- Haskell.Prim.List.unzip
d_unzip_182 ::
  () ->
  () ->
  [MAlonzo.Code.Haskell.Prim.Tuple.T__'215'__10] ->
  MAlonzo.Code.Haskell.Prim.Tuple.T__'215'__10
d_unzip_182 ~v0 ~v1 v2 = du_unzip_182 v2
du_unzip_182 ::
  [MAlonzo.Code.Haskell.Prim.Tuple.T__'215'__10] ->
  MAlonzo.Code.Haskell.Prim.Tuple.T__'215'__10
du_unzip_182 v0 =
  case coe v0 of
    [] ->
      coe
        MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24
        (coe v0)
        (coe v0)
    (:) v1 v2 ->
      case coe v1 of
        MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24 v3 v4 ->
          coe
            MAlonzo.Code.Haskell.Prim.du__'36'__48
            ( coe
                MAlonzo.Code.Haskell.Prim.Tuple.du__'42''42''42'__74
                (coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3))
                (coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4))
            )
            (coe du_unzip_182 (coe v2))
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.List.unzip3
d_unzip3_194 ::
  () ->
  () ->
  () ->
  [MAlonzo.Code.Haskell.Prim.Tuple.T__'215'_'215'__32] ->
  MAlonzo.Code.Haskell.Prim.Tuple.T__'215'_'215'__32
d_unzip3_194 ~v0 ~v1 ~v2 v3 = du_unzip3_194 v3
du_unzip3_194 ::
  [MAlonzo.Code.Haskell.Prim.Tuple.T__'215'_'215'__32] ->
  MAlonzo.Code.Haskell.Prim.Tuple.T__'215'_'215'__32
du_unzip3_194 v0 =
  case coe v0 of
    [] ->
      coe
        MAlonzo.Code.Haskell.Prim.Tuple.C__'44'_'44'__40
        (coe v0)
        (coe v0)
        (coe v0)
    (:) v1 v2 ->
      case coe v1 of
        MAlonzo.Code.Haskell.Prim.Tuple.C__'44'_'44'__40 v3 v4 v5 ->
          coe
            MAlonzo.Code.Haskell.Prim.du_case_of__58
            (coe du_unzip3_194 (coe v2))
            ( coe
                ( \v6 v7 ->
                    case coe v6 of
                      MAlonzo.Code.Haskell.Prim.Tuple.C__'44'_'44'__40 v8 v9 v10 ->
                        coe
                          MAlonzo.Code.Haskell.Prim.Tuple.C__'44'_'44'__40
                          ( coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe v3)
                              (coe v8)
                          )
                          ( coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe v4)
                              (coe v9)
                          )
                          ( coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe v5)
                              (coe v10)
                          )
                      _ -> MAlonzo.RTE.mazUnreachableError
                )
            )
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.List.takeNat
d_takeNat_212 :: () -> Integer -> [AgdaAny] -> [AgdaAny]
d_takeNat_212 ~v0 v1 v2 = du_takeNat_212 v1 v2
du_takeNat_212 :: Integer -> [AgdaAny] -> [AgdaAny]
du_takeNat_212 v0 v1 =
  case coe v1 of
    [] -> coe v1
    (:) v2 v3 ->
      case coe v0 of
        0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
        _ ->
          let v4 = subInt (coe v0) (coe (1 :: Integer))
           in coe
                ( coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe v2)
                    (coe du_takeNat_212 (coe v4) (coe v3))
                )
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.List.take
d_take_226 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Int.T_Int_6 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny]
d_take_226 ~v0 v1 ~v2 v3 = du_take_226 v1 v3
du_take_226 ::
  MAlonzo.Code.Haskell.Prim.Int.T_Int_6 -> [AgdaAny] -> [AgdaAny]
du_take_226 v0 v1 =
  coe
    du_takeNat_212
    (coe MAlonzo.Code.Haskell.Prim.Int.du_intToNat_128 (coe v0))
    (coe v1)

-- Haskell.Prim.List.dropNat
d_dropNat_232 :: () -> Integer -> [AgdaAny] -> [AgdaAny]
d_dropNat_232 ~v0 v1 v2 = du_dropNat_232 v1 v2
du_dropNat_232 :: Integer -> [AgdaAny] -> [AgdaAny]
du_dropNat_232 v0 v1 =
  case coe v1 of
    [] -> coe v1
    (:) v2 v3 ->
      case coe v0 of
        0 -> coe v1
        _ ->
          let v4 = subInt (coe v0) (coe (1 :: Integer))
           in coe (coe du_dropNat_232 (coe v4) (coe v3))
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.List.drop
d_drop_244 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Int.T_Int_6 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny]
d_drop_244 ~v0 v1 ~v2 v3 = du_drop_244 v1 v3
du_drop_244 ::
  MAlonzo.Code.Haskell.Prim.Int.T_Int_6 -> [AgdaAny] -> [AgdaAny]
du_drop_244 v0 v1 =
  coe
    du_dropNat_232
    (coe MAlonzo.Code.Haskell.Prim.Int.du_intToNat_128 (coe v0))
    (coe v1)

-- Haskell.Prim.List.splitAtNat
d_splitAtNat_252 ::
  () ->
  Integer ->
  [AgdaAny] ->
  MAlonzo.Code.Haskell.Prim.Tuple.T__'215'__10
d_splitAtNat_252 ~v0 v1 v2 = du_splitAtNat_252 v1 v2
du_splitAtNat_252 ::
  Integer ->
  [AgdaAny] ->
  MAlonzo.Code.Haskell.Prim.Tuple.T__'215'__10
du_splitAtNat_252 v0 v1 =
  case coe v1 of
    [] ->
      coe
        MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24
        (coe v1)
        (coe v1)
    (:) v2 v3 ->
      case coe v0 of
        0 ->
          coe
            MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
            (coe v1)
        _ ->
          let v4 = subInt (coe v0) (coe (1 :: Integer))
           in coe
                ( coe
                    MAlonzo.Code.Haskell.Prim.Tuple.du_first_58
                    (coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2))
                    (coe du_splitAtNat_252 (coe v4) (coe v3))
                )
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.List.splitAt
d_splitAt_266 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Int.T_Int_6 ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Haskell.Prim.Tuple.T__'215'__10
d_splitAt_266 ~v0 v1 ~v2 v3 = du_splitAt_266 v1 v3
du_splitAt_266 ::
  MAlonzo.Code.Haskell.Prim.Int.T_Int_6 ->
  [AgdaAny] ->
  MAlonzo.Code.Haskell.Prim.Tuple.T__'215'__10
du_splitAt_266 v0 v1 =
  coe
    du_splitAtNat_252
    (coe MAlonzo.Code.Haskell.Prim.Int.du_intToNat_128 (coe v0))
    (coe v1)

-- Haskell.Prim.List.head
d_head_274 ::
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Haskell.Prim.T_NonEmpty_136 ->
  AgdaAny
d_head_274 ~v0 v1 ~v2 = du_head_274 v1
du_head_274 :: [AgdaAny] -> AgdaAny
du_head_274 v0 =
  case coe v0 of
    (:) v1 v2 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.List.tail
d_tail_280 ::
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Haskell.Prim.T_NonEmpty_136 ->
  [AgdaAny]
d_tail_280 ~v0 v1 ~v2 = du_tail_280 v1
du_tail_280 :: [AgdaAny] -> [AgdaAny]
du_tail_280 v0 =
  case coe v0 of
    (:) v1 v2 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.List.last
d_last_286 ::
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Haskell.Prim.T_NonEmpty_136 ->
  AgdaAny
d_last_286 ~v0 v1 ~v2 = du_last_286 v1
du_last_286 :: [AgdaAny] -> AgdaAny
du_last_286 v0 =
  case coe v0 of
    (:) v1 v2 ->
      case coe v2 of
        [] -> coe v1
        (:) v3 v4 -> coe du_last_286 (coe v2)
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.List.init
d_init_294 ::
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Haskell.Prim.T_NonEmpty_136 ->
  [AgdaAny]
d_init_294 ~v0 v1 ~v2 = du_init_294 v1
du_init_294 :: [AgdaAny] -> [AgdaAny]
du_init_294 v0 =
  case coe v0 of
    (:) v1 v2 ->
      case coe v2 of
        [] -> coe v2
        (:) v3 v4 ->
          coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe v1)
            (coe du_init_294 (coe v2))
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError
