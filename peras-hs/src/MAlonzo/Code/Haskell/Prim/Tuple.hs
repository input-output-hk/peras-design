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

module MAlonzo.Code.Haskell.Prim.Tuple where

import qualified Data.Text
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

-- Haskell.Prim.Tuple._×_
d__'215'__10 a0 a1 = ()
data T__'215'__10 = C__'44'__24 AgdaAny AgdaAny

-- Haskell.Prim.Tuple._×_.fst
d_fst_20 :: T__'215'__10 -> AgdaAny
d_fst_20 v0 =
  case coe v0 of
    C__'44'__24 v1 v2 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Tuple._×_.snd
d_snd_22 :: T__'215'__10 -> AgdaAny
d_snd_22 v0 =
  case coe v0 of
    C__'44'__24 v1 v2 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Tuple._×_×_
d__'215'_'215'__32 a0 a1 a2 = ()
data T__'215'_'215'__32 = C__'44'_'44'__40 AgdaAny AgdaAny AgdaAny

-- Haskell.Prim.Tuple.uncurry
d_uncurry_42 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T__'215'__10 ->
  AgdaAny
d_uncurry_42 ~v0 ~v1 ~v2 v3 v4 = du_uncurry_42 v3 v4
du_uncurry_42 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> T__'215'__10 -> AgdaAny
du_uncurry_42 v0 v1 =
  case coe v1 of
    C__'44'__24 v2 v3 -> coe v0 v2 v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Tuple.curry
d_curry_50 ::
  () ->
  () ->
  () ->
  (T__'215'__10 -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d_curry_50 ~v0 ~v1 ~v2 v3 v4 v5 = du_curry_50 v3 v4 v5
du_curry_50 ::
  (T__'215'__10 -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_curry_50 v0 v1 v2 = coe v0 (coe C__'44'__24 (coe v1) (coe v2))

-- Haskell.Prim.Tuple.first
d_first_58 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  T__'215'__10 ->
  T__'215'__10
d_first_58 ~v0 ~v1 ~v2 v3 v4 = du_first_58 v3 v4
du_first_58 :: (AgdaAny -> AgdaAny) -> T__'215'__10 -> T__'215'__10
du_first_58 v0 v1 =
  case coe v1 of
    C__'44'__24 v2 v3 -> coe C__'44'__24 (coe v0 v2) (coe v3)
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Tuple.second
d_second_66 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  T__'215'__10 ->
  T__'215'__10
d_second_66 ~v0 ~v1 ~v2 v3 v4 = du_second_66 v3 v4
du_second_66 ::
  (AgdaAny -> AgdaAny) -> T__'215'__10 -> T__'215'__10
du_second_66 v0 v1 =
  case coe v1 of
    C__'44'__24 v2 v3 -> coe C__'44'__24 (coe v2) (coe v0 v3)
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Tuple._***_
d__'42''42''42'__74 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T__'215'__10 ->
  T__'215'__10
d__'42''42''42'__74 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 =
  du__'42''42''42'__74 v4 v5 v6
du__'42''42''42'__74 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T__'215'__10 ->
  T__'215'__10
du__'42''42''42'__74 v0 v1 v2 =
  case coe v2 of
    C__'44'__24 v3 v4 -> coe C__'44'__24 (coe v0 v3) (coe v1 v4)
    _ -> MAlonzo.RTE.mazUnreachableError
