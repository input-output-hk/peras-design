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

module MAlonzo.Code.Haskell.Prelude where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Haskell.Prim
import qualified MAlonzo.Code.Haskell.Prim.Eq
import qualified MAlonzo.Code.Haskell.Prim.Foldable
import qualified MAlonzo.Code.Haskell.Prim.Int
import qualified MAlonzo.Code.Haskell.Prim.Maybe
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

-- Haskell.Prelude._$!_
d__'36''33'__4 ::
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'36''33'__4 ~v0 ~v1 = du__'36''33'__4
du__'36''33'__4 :: (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'36''33'__4 = coe MAlonzo.Code.Haskell.Prim.du__'36'__48

-- Haskell.Prelude.seq
d_seq_6 :: () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_seq_6 ~v0 ~v1 = du_seq_6
du_seq_6 :: AgdaAny -> AgdaAny -> AgdaAny
du_seq_6 = let v0 = \v0 -> v0 in coe (coe (\v1 -> v0))

-- Haskell.Prelude.asTypeOf
d_asTypeOf_8 :: () -> AgdaAny -> AgdaAny -> AgdaAny
d_asTypeOf_8 ~v0 v1 ~v2 = du_asTypeOf_8 v1
du_asTypeOf_8 :: AgdaAny -> AgdaAny
du_asTypeOf_8 v0 = coe v0

-- Haskell.Prelude.undefined
d_undefined_14 ::
  () -> MAlonzo.Code.Haskell.Prim.T_'8869'_90 -> AgdaAny
d_undefined_14 ~v0 ~v1 = du_undefined_14
du_undefined_14 :: AgdaAny
du_undefined_14 = MAlonzo.RTE.mazUnreachableError

-- Haskell.Prelude.error
d_error_18 ::
  () ->
  MAlonzo.Code.Haskell.Prim.T_'8869'_90 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  AgdaAny
d_error_18 ~v0 ~v1 ~v2 = du_error_18
du_error_18 :: AgdaAny
du_error_18 = MAlonzo.RTE.mazUnreachableError

-- Haskell.Prelude.errorWithoutStackTrace
d_errorWithoutStackTrace_24 ::
  () ->
  MAlonzo.Code.Haskell.Prim.T_'8869'_90 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  AgdaAny
d_errorWithoutStackTrace_24 ~v0 ~v1 ~v2 =
  du_errorWithoutStackTrace_24
du_errorWithoutStackTrace_24 :: AgdaAny
du_errorWithoutStackTrace_24 = MAlonzo.RTE.mazUnreachableError

-- Haskell.Prelude.reverse
d_reverse_28 :: () -> [AgdaAny] -> [AgdaAny]
d_reverse_28 ~v0 = du_reverse_28
du_reverse_28 :: [AgdaAny] -> [AgdaAny]
du_reverse_28 =
  coe
    MAlonzo.Code.Haskell.Prim.Foldable.du_foldl_170
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
    ( coe
        MAlonzo.Code.Haskell.Prim.du_flip_36
        (coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22)
    )
    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)

-- Haskell.Prelude._!!ᴺ_
d__'33''33''7482'__34 ::
  () ->
  [AgdaAny] ->
  Integer ->
  MAlonzo.Code.Haskell.Prim.T_IsTrue_126 ->
  AgdaAny
d__'33''33''7482'__34 ~v0 v1 v2 ~v3 = du__'33''33''7482'__34 v1 v2
du__'33''33''7482'__34 :: [AgdaAny] -> Integer -> AgdaAny
du__'33''33''7482'__34 v0 v1 =
  case coe v0 of
    (:) v2 v3 ->
      case coe v1 of
        0 -> coe v2
        _ ->
          let v4 = subInt (coe v1) (coe (1 :: Integer))
           in coe (coe du__'33''33''7482'__34 (coe v3) (coe v4))
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prelude._!!_
d__'33''33'__54 ::
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Haskell.Prim.Int.T_Int_6 ->
  AgdaAny ->
  MAlonzo.Code.Haskell.Prim.T_IsTrue_126 ->
  AgdaAny
d__'33''33'__54 ~v0 v1 v2 ~v3 ~v4 = du__'33''33'__54 v1 v2
du__'33''33'__54 ::
  [AgdaAny] -> MAlonzo.Code.Haskell.Prim.Int.T_Int_6 -> AgdaAny
du__'33''33'__54 v0 v1 =
  coe
    du__'33''33''7482'__34
    (coe v0)
    (coe MAlonzo.Code.Haskell.Prim.Int.du_intToNat_128 (coe v1))

-- Haskell.Prelude.lookup
d_lookup_60 ::
  () ->
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  AgdaAny ->
  [MAlonzo.Code.Haskell.Prim.Tuple.T__'215'__10] ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10
d_lookup_60 ~v0 ~v1 v2 v3 v4 = du_lookup_60 v2 v3 v4
du_lookup_60 ::
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  AgdaAny ->
  [MAlonzo.Code.Haskell.Prim.Tuple.T__'215'__10] ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10
du_lookup_60 v0 v1 v2 =
  case coe v2 of
    [] -> coe MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16
    (:) v3 v4 ->
      case coe v3 of
        MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24 v5 v6 ->
          coe
            MAlonzo.Code.Haskell.Prim.du_if_then_else__68
            (coe MAlonzo.Code.Haskell.Prim.Eq.d__'61''61'__14 v0 v1 v5)
            ( coe
                (\v7 -> coe MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 (coe v6))
            )
            (coe (\v7 -> coe du_lookup_60 (coe v0) (coe v1) (coe v4)))
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prelude.coerce
d_coerce_76 ::
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny
d_coerce_76 ~v0 ~v1 ~v2 v3 = du_coerce_76 v3
du_coerce_76 :: AgdaAny -> AgdaAny
du_coerce_76 v0 = coe v0
