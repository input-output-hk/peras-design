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

module MAlonzo.Code.Haskell.Prim.Foldable where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Haskell.Prim
import qualified MAlonzo.Code.Haskell.Prim.Bool
import qualified MAlonzo.Code.Haskell.Prim.Either
import qualified MAlonzo.Code.Haskell.Prim.Eq
import qualified MAlonzo.Code.Haskell.Prim.Int
import qualified MAlonzo.Code.Haskell.Prim.Maybe
import qualified MAlonzo.Code.Haskell.Prim.Monoid
import qualified MAlonzo.Code.Haskell.Prim.Num
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

-- Haskell.Prim.Foldable.Foldable
d_Foldable_8 a0 = ()
data T_Foldable_8
  = C_Foldable'46'constructor_2791
      ( () ->
        () ->
        MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
        (AgdaAny -> AgdaAny) ->
        AgdaAny ->
        AgdaAny
      )
      ( () ->
        () ->
        (AgdaAny -> AgdaAny -> AgdaAny) ->
        AgdaAny ->
        AgdaAny ->
        AgdaAny
      )
      ( () ->
        () ->
        (AgdaAny -> AgdaAny -> AgdaAny) ->
        AgdaAny ->
        AgdaAny ->
        AgdaAny
      )
      (() -> (AgdaAny -> Bool) -> AgdaAny -> Bool)
      (() -> (AgdaAny -> Bool) -> AgdaAny -> Bool)
      (AgdaAny -> Bool)
      (() -> AgdaAny -> Bool)
      (AgdaAny -> Bool)
      (() -> AgdaAny -> [AgdaAny])
      (() -> () -> (AgdaAny -> [AgdaAny]) -> AgdaAny -> [AgdaAny])
      ( () ->
        MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
        AgdaAny ->
        AgdaAny ->
        Bool
      )
      ( () ->
        MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
        AgdaAny ->
        AgdaAny ->
        Bool
      )
      (() -> AgdaAny -> [AgdaAny])
      ( () ->
        MAlonzo.Code.Haskell.Prim.Num.T_Num_8 ->
        AgdaAny ->
        AgdaAny
      )
      ( () ->
        MAlonzo.Code.Haskell.Prim.Num.T_Num_8 ->
        AgdaAny ->
        AgdaAny
      )
      (() -> AgdaAny -> MAlonzo.Code.Haskell.Prim.Int.T_Int_6)

-- Haskell.Prim.Foldable.Foldable.foldMap
d_foldMap_48 ::
  T_Foldable_8 ->
  () ->
  () ->
  MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d_foldMap_48 v0 =
  case coe v0 of
    C_Foldable'46'constructor_2791 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
      coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Foldable.Foldable.foldr
d_foldr_50 ::
  T_Foldable_8 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d_foldr_50 v0 =
  case coe v0 of
    C_Foldable'46'constructor_2791 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
      coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Foldable.Foldable.foldl
d_foldl_52 ::
  T_Foldable_8 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d_foldl_52 v0 =
  case coe v0 of
    C_Foldable'46'constructor_2791 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
      coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Foldable.Foldable.any
d_any_54 ::
  T_Foldable_8 -> () -> (AgdaAny -> Bool) -> AgdaAny -> Bool
d_any_54 v0 =
  case coe v0 of
    C_Foldable'46'constructor_2791 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
      coe v4
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Foldable.Foldable.all
d_all_56 ::
  T_Foldable_8 -> () -> (AgdaAny -> Bool) -> AgdaAny -> Bool
d_all_56 v0 =
  case coe v0 of
    C_Foldable'46'constructor_2791 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
      coe v5
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Foldable.Foldable.and
d_and_58 :: T_Foldable_8 -> AgdaAny -> Bool
d_and_58 v0 =
  case coe v0 of
    C_Foldable'46'constructor_2791 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
      coe v6
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Foldable.Foldable.null
d_null_60 :: T_Foldable_8 -> () -> AgdaAny -> Bool
d_null_60 v0 =
  case coe v0 of
    C_Foldable'46'constructor_2791 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
      coe v7
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Foldable.Foldable.or
d_or_62 :: T_Foldable_8 -> AgdaAny -> Bool
d_or_62 v0 =
  case coe v0 of
    C_Foldable'46'constructor_2791 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
      coe v8
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Foldable.Foldable.concat
d_concat_64 :: T_Foldable_8 -> () -> AgdaAny -> [AgdaAny]
d_concat_64 v0 =
  case coe v0 of
    C_Foldable'46'constructor_2791 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
      coe v9
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Foldable.Foldable.concatMap
d_concatMap_66 ::
  T_Foldable_8 ->
  () ->
  () ->
  (AgdaAny -> [AgdaAny]) ->
  AgdaAny ->
  [AgdaAny]
d_concatMap_66 v0 =
  case coe v0 of
    C_Foldable'46'constructor_2791 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
      coe v10
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Foldable.Foldable.elem
d_elem_68 ::
  T_Foldable_8 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  AgdaAny ->
  AgdaAny ->
  Bool
d_elem_68 v0 =
  case coe v0 of
    C_Foldable'46'constructor_2791 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
      coe v11
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Foldable.Foldable.notElem
d_notElem_70 ::
  T_Foldable_8 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  AgdaAny ->
  AgdaAny ->
  Bool
d_notElem_70 v0 =
  case coe v0 of
    C_Foldable'46'constructor_2791 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
      coe v12
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Foldable.Foldable.toList
d_toList_72 :: T_Foldable_8 -> () -> AgdaAny -> [AgdaAny]
d_toList_72 v0 =
  case coe v0 of
    C_Foldable'46'constructor_2791 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
      coe v13
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Foldable.Foldable.sum
d_sum_76 ::
  T_Foldable_8 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Num.T_Num_8 ->
  AgdaAny ->
  AgdaAny
d_sum_76 v0 =
  case coe v0 of
    C_Foldable'46'constructor_2791 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
      coe v14
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Foldable.Foldable.product
d_product_80 ::
  T_Foldable_8 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Num.T_Num_8 ->
  AgdaAny ->
  AgdaAny
d_product_80 v0 =
  case coe v0 of
    C_Foldable'46'constructor_2791 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
      coe v15
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Foldable.Foldable.length
d_length_82 ::
  T_Foldable_8 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Haskell.Prim.Int.T_Int_6
d_length_82 v0 =
  case coe v0 of
    C_Foldable'46'constructor_2791 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
      coe v16
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Foldable.DefaultFoldable
d_DefaultFoldable_86 a0 = ()
newtype T_DefaultFoldable_86
  = C_DefaultFoldable'46'constructor_4805
      ( () ->
        () ->
        MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
        (AgdaAny -> AgdaAny) ->
        AgdaAny ->
        AgdaAny
      )

-- Haskell.Prim.Foldable.DefaultFoldable.M.all
d_all_128 ::
  T_Foldable_8 -> () -> (AgdaAny -> Bool) -> AgdaAny -> Bool
d_all_128 v0 = coe d_all_56 (coe v0)

-- Haskell.Prim.Foldable.DefaultFoldable.M.and
d_and_130 :: T_Foldable_8 -> AgdaAny -> Bool
d_and_130 v0 = coe d_and_58 (coe v0)

-- Haskell.Prim.Foldable.DefaultFoldable.M.any
d_any_132 ::
  T_Foldable_8 -> () -> (AgdaAny -> Bool) -> AgdaAny -> Bool
d_any_132 v0 = coe d_any_54 (coe v0)

-- Haskell.Prim.Foldable.DefaultFoldable.M.concat
d_concat_134 :: T_Foldable_8 -> () -> AgdaAny -> [AgdaAny]
d_concat_134 v0 = coe d_concat_64 (coe v0)

-- Haskell.Prim.Foldable.DefaultFoldable.M.concatMap
d_concatMap_136 ::
  T_Foldable_8 ->
  () ->
  () ->
  (AgdaAny -> [AgdaAny]) ->
  AgdaAny ->
  [AgdaAny]
d_concatMap_136 v0 = coe d_concatMap_66 (coe v0)

-- Haskell.Prim.Foldable.DefaultFoldable.M.elem
d_elem_138 ::
  T_Foldable_8 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  AgdaAny ->
  AgdaAny ->
  Bool
d_elem_138 v0 = coe d_elem_68 (coe v0)

-- Haskell.Prim.Foldable.DefaultFoldable.M.foldMap
d_foldMap_140 ::
  T_Foldable_8 ->
  () ->
  () ->
  MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d_foldMap_140 v0 = coe d_foldMap_48 (coe v0)

-- Haskell.Prim.Foldable.DefaultFoldable.M.foldl
d_foldl_142 ::
  T_Foldable_8 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d_foldl_142 v0 = coe d_foldl_52 (coe v0)

-- Haskell.Prim.Foldable.DefaultFoldable.M.foldr
d_foldr_144 ::
  T_Foldable_8 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d_foldr_144 v0 = coe d_foldr_50 (coe v0)

-- Haskell.Prim.Foldable.DefaultFoldable.M.length
d_length_146 ::
  T_Foldable_8 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Haskell.Prim.Int.T_Int_6
d_length_146 v0 = coe d_length_82 (coe v0)

-- Haskell.Prim.Foldable.DefaultFoldable.M.notElem
d_notElem_148 ::
  T_Foldable_8 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  AgdaAny ->
  AgdaAny ->
  Bool
d_notElem_148 v0 = coe d_notElem_70 (coe v0)

-- Haskell.Prim.Foldable.DefaultFoldable.M.null
d_null_150 :: T_Foldable_8 -> () -> AgdaAny -> Bool
d_null_150 v0 = coe d_null_60 (coe v0)

-- Haskell.Prim.Foldable.DefaultFoldable.M.or
d_or_152 :: T_Foldable_8 -> AgdaAny -> Bool
d_or_152 v0 = coe d_or_62 (coe v0)

-- Haskell.Prim.Foldable.DefaultFoldable.M.product
d_product_154 ::
  T_Foldable_8 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Num.T_Num_8 ->
  AgdaAny ->
  AgdaAny
d_product_154 v0 = coe d_product_80 (coe v0)

-- Haskell.Prim.Foldable.DefaultFoldable.M.sum
d_sum_156 ::
  T_Foldable_8 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Num.T_Num_8 ->
  AgdaAny ->
  AgdaAny
d_sum_156 v0 = coe d_sum_76 (coe v0)

-- Haskell.Prim.Foldable.DefaultFoldable.M.toList
d_toList_158 :: T_Foldable_8 -> () -> AgdaAny -> [AgdaAny]
d_toList_158 v0 = coe d_toList_72 (coe v0)

-- Haskell.Prim.Foldable.DefaultFoldable.foldMap
d_foldMap_160 ::
  T_DefaultFoldable_86 ->
  () ->
  () ->
  MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d_foldMap_160 v0 =
  case coe v0 of
    C_DefaultFoldable'46'constructor_4805 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Foldable.DefaultFoldable.foldr
d_foldr_162 ::
  (() -> ()) ->
  T_DefaultFoldable_86 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d_foldr_162 ~v0 v1 ~v2 ~v3 v4 v5 v6 = du_foldr_162 v1 v4 v5 v6
du_foldr_162 ::
  T_DefaultFoldable_86 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
du_foldr_162 v0 v1 v2 v3 =
  coe
    d_foldMap_160
    v0
    erased
    erased
    (coe MAlonzo.Code.Haskell.Prim.Monoid.du_MonoidEndo_172)
    v1
    v3
    v2

-- Haskell.Prim.Foldable.DefaultFoldable.foldl
d_foldl_170 ::
  (() -> ()) ->
  T_DefaultFoldable_86 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d_foldl_170 ~v0 v1 ~v2 ~v3 v4 v5 v6 = du_foldl_170 v1 v4 v5 v6
du_foldl_170 ::
  T_DefaultFoldable_86 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
du_foldl_170 v0 v1 v2 v3 =
  coe
    d_foldMap_160
    v0
    erased
    erased
    ( coe
        MAlonzo.Code.Haskell.Prim.Monoid.du_MonoidEndo'7506''7510'_176
    )
    (coe MAlonzo.Code.Haskell.Prim.du_flip_36 (coe v1))
    v3
    v2

-- Haskell.Prim.Foldable.DefaultFoldable.any
d_any_178 ::
  (() -> ()) ->
  T_DefaultFoldable_86 ->
  () ->
  (AgdaAny -> Bool) ->
  AgdaAny ->
  Bool
d_any_178 ~v0 v1 ~v2 = du_any_178 v1
du_any_178 ::
  T_DefaultFoldable_86 -> (AgdaAny -> Bool) -> AgdaAny -> Bool
du_any_178 v0 =
  coe
    d_foldMap_160
    v0
    erased
    erased
    MAlonzo.Code.Haskell.Prim.Monoid.d_MonoidDisj_184

-- Haskell.Prim.Foldable.DefaultFoldable.all
d_all_180 ::
  (() -> ()) ->
  T_DefaultFoldable_86 ->
  () ->
  (AgdaAny -> Bool) ->
  AgdaAny ->
  Bool
d_all_180 ~v0 v1 ~v2 = du_all_180 v1
du_all_180 ::
  T_DefaultFoldable_86 -> (AgdaAny -> Bool) -> AgdaAny -> Bool
du_all_180 v0 =
  coe
    d_foldMap_160
    v0
    erased
    erased
    MAlonzo.Code.Haskell.Prim.Monoid.d_MonoidConj_180

-- Haskell.Prim.Foldable.DefaultFoldable.and
d_and_182 :: (() -> ()) -> T_DefaultFoldable_86 -> AgdaAny -> Bool
d_and_182 ~v0 v1 = du_and_182 v1
du_and_182 :: T_DefaultFoldable_86 -> AgdaAny -> Bool
du_and_182 v0 = coe du_all_180 v0 (\v1 -> v1)

-- Haskell.Prim.Foldable.DefaultFoldable.or
d_or_184 :: (() -> ()) -> T_DefaultFoldable_86 -> AgdaAny -> Bool
d_or_184 ~v0 v1 = du_or_184 v1
du_or_184 :: T_DefaultFoldable_86 -> AgdaAny -> Bool
du_or_184 v0 = coe du_any_178 v0 (\v1 -> v1)

-- Haskell.Prim.Foldable.DefaultFoldable.null
d_null_186 ::
  (() -> ()) -> T_DefaultFoldable_86 -> () -> AgdaAny -> Bool
d_null_186 ~v0 v1 ~v2 = du_null_186 v1
du_null_186 :: T_DefaultFoldable_86 -> AgdaAny -> Bool
du_null_186 v0 =
  coe
    du_all_180
    v0
    ( let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
       in coe (\v2 -> v1)
    )

-- Haskell.Prim.Foldable.DefaultFoldable.concat
d_concat_188 ::
  (() -> ()) -> T_DefaultFoldable_86 -> () -> AgdaAny -> [AgdaAny]
d_concat_188 ~v0 v1 ~v2 = du_concat_188 v1
du_concat_188 :: T_DefaultFoldable_86 -> AgdaAny -> [AgdaAny]
du_concat_188 v0 =
  coe
    d_foldMap_160
    v0
    erased
    erased
    ( coe
        MAlonzo.Code.Haskell.Prim.Monoid.du_mempty'61'__126
        (coe MAlonzo.Code.Haskell.Prim.Monoid.du_iSemigroupList_20)
        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
    )
    (\v1 -> v1)

-- Haskell.Prim.Foldable.DefaultFoldable.concatMap
d_concatMap_190 ::
  (() -> ()) ->
  T_DefaultFoldable_86 ->
  () ->
  () ->
  (AgdaAny -> [AgdaAny]) ->
  AgdaAny ->
  [AgdaAny]
d_concatMap_190 ~v0 v1 ~v2 ~v3 = du_concatMap_190 v1
du_concatMap_190 ::
  T_DefaultFoldable_86 ->
  (AgdaAny -> [AgdaAny]) ->
  AgdaAny ->
  [AgdaAny]
du_concatMap_190 v0 =
  coe
    d_foldMap_160
    v0
    erased
    erased
    ( coe
        MAlonzo.Code.Haskell.Prim.Monoid.du_mempty'61'__126
        (coe MAlonzo.Code.Haskell.Prim.Monoid.du_iSemigroupList_20)
        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
    )

-- Haskell.Prim.Foldable.DefaultFoldable.elem
d_elem_192 ::
  (() -> ()) ->
  T_DefaultFoldable_86 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  AgdaAny ->
  AgdaAny ->
  Bool
d_elem_192 ~v0 v1 ~v2 v3 v4 = du_elem_192 v1 v3 v4
du_elem_192 ::
  T_DefaultFoldable_86 ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  AgdaAny ->
  AgdaAny ->
  Bool
du_elem_192 v0 v1 v2 =
  coe
    d_foldMap_160
    v0
    erased
    erased
    MAlonzo.Code.Haskell.Prim.Monoid.d_MonoidDisj_184
    (coe MAlonzo.Code.Haskell.Prim.Eq.d__'61''61'__14 v1 v2)

-- Haskell.Prim.Foldable.DefaultFoldable.notElem
d_notElem_198 ::
  (() -> ()) ->
  T_DefaultFoldable_86 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  AgdaAny ->
  AgdaAny ->
  Bool
d_notElem_198 ~v0 v1 ~v2 v3 v4 v5 = du_notElem_198 v1 v3 v4 v5
du_notElem_198 ::
  T_DefaultFoldable_86 ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  AgdaAny ->
  AgdaAny ->
  Bool
du_notElem_198 v0 v1 v2 v3 =
  coe
    MAlonzo.Code.Haskell.Prim.Bool.d_not_14
    (coe du_elem_192 v0 v1 v2 v3)

-- Haskell.Prim.Foldable.DefaultFoldable.toList
d_toList_204 ::
  (() -> ()) -> T_DefaultFoldable_86 -> () -> AgdaAny -> [AgdaAny]
d_toList_204 ~v0 v1 ~v2 = du_toList_204 v1
du_toList_204 :: T_DefaultFoldable_86 -> AgdaAny -> [AgdaAny]
du_toList_204 v0 =
  coe
    du_foldr_162
    (coe v0)
    (coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22)
    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)

-- Haskell.Prim.Foldable.DefaultFoldable.sum
d_sum_208 ::
  (() -> ()) ->
  T_DefaultFoldable_86 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Num.T_Num_8 ->
  AgdaAny ->
  AgdaAny
d_sum_208 ~v0 v1 ~v2 v3 = du_sum_208 v1 v3
du_sum_208 ::
  T_DefaultFoldable_86 ->
  MAlonzo.Code.Haskell.Prim.Num.T_Num_8 ->
  AgdaAny ->
  AgdaAny
du_sum_208 v0 v1 =
  coe
    d_foldMap_160
    v0
    erased
    erased
    (coe MAlonzo.Code.Haskell.Prim.Num.du_MonoidSum_224 (coe v1))
    (\v2 -> v2)

-- Haskell.Prim.Foldable.DefaultFoldable.product
d_product_212 ::
  (() -> ()) ->
  T_DefaultFoldable_86 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Num.T_Num_8 ->
  AgdaAny ->
  AgdaAny
d_product_212 ~v0 v1 ~v2 v3 = du_product_212 v1 v3
du_product_212 ::
  T_DefaultFoldable_86 ->
  MAlonzo.Code.Haskell.Prim.Num.T_Num_8 ->
  AgdaAny ->
  AgdaAny
du_product_212 v0 v1 =
  coe
    d_foldMap_160
    v0
    erased
    erased
    (coe MAlonzo.Code.Haskell.Prim.Num.du_MonoidProduct_242 (coe v1))
    (\v2 -> v2)

-- Haskell.Prim.Foldable.DefaultFoldable.length
d_length_214 ::
  (() -> ()) ->
  T_DefaultFoldable_86 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Haskell.Prim.Int.T_Int_6
d_length_214 ~v0 v1 ~v2 = du_length_214 v1
du_length_214 ::
  T_DefaultFoldable_86 ->
  AgdaAny ->
  MAlonzo.Code.Haskell.Prim.Int.T_Int_6
du_length_214 v0 =
  coe
    d_foldMap_160
    v0
    erased
    erased
    ( coe
        MAlonzo.Code.Haskell.Prim.Num.du_MonoidSum_224
        (coe MAlonzo.Code.Haskell.Prim.Num.d_iNumInt_130)
    )
    ( let v1 =
            coe
              MAlonzo.Code.Haskell.Prim.Int.C_int64_8
              (coe (1 :: MAlonzo.RTE.Word64))
       in coe (\v2 -> v1)
    )

-- Haskell.Prim.Foldable._.all
d_all_218 ::
  T_Foldable_8 -> () -> (AgdaAny -> Bool) -> AgdaAny -> Bool
d_all_218 v0 = coe d_all_56 (coe v0)

-- Haskell.Prim.Foldable._.and
d_and_220 :: T_Foldable_8 -> AgdaAny -> Bool
d_and_220 v0 = coe d_and_58 (coe v0)

-- Haskell.Prim.Foldable._.any
d_any_222 ::
  T_Foldable_8 -> () -> (AgdaAny -> Bool) -> AgdaAny -> Bool
d_any_222 v0 = coe d_any_54 (coe v0)

-- Haskell.Prim.Foldable._.concat
d_concat_224 :: T_Foldable_8 -> () -> AgdaAny -> [AgdaAny]
d_concat_224 v0 = coe d_concat_64 (coe v0)

-- Haskell.Prim.Foldable._.concatMap
d_concatMap_226 ::
  T_Foldable_8 ->
  () ->
  () ->
  (AgdaAny -> [AgdaAny]) ->
  AgdaAny ->
  [AgdaAny]
d_concatMap_226 v0 = coe d_concatMap_66 (coe v0)

-- Haskell.Prim.Foldable._.elem
d_elem_228 ::
  T_Foldable_8 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  AgdaAny ->
  AgdaAny ->
  Bool
d_elem_228 v0 = coe d_elem_68 (coe v0)

-- Haskell.Prim.Foldable._.foldMap
d_foldMap_230 ::
  T_Foldable_8 ->
  () ->
  () ->
  MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d_foldMap_230 v0 = coe d_foldMap_48 (coe v0)

-- Haskell.Prim.Foldable._.foldl
d_foldl_232 ::
  T_Foldable_8 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d_foldl_232 v0 = coe d_foldl_52 (coe v0)

-- Haskell.Prim.Foldable._.foldr
d_foldr_234 ::
  T_Foldable_8 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d_foldr_234 v0 = coe d_foldr_50 (coe v0)

-- Haskell.Prim.Foldable._.length
d_length_236 ::
  T_Foldable_8 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Haskell.Prim.Int.T_Int_6
d_length_236 v0 = coe d_length_82 (coe v0)

-- Haskell.Prim.Foldable._.notElem
d_notElem_238 ::
  T_Foldable_8 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  AgdaAny ->
  AgdaAny ->
  Bool
d_notElem_238 v0 = coe d_notElem_70 (coe v0)

-- Haskell.Prim.Foldable._.null
d_null_240 :: T_Foldable_8 -> () -> AgdaAny -> Bool
d_null_240 v0 = coe d_null_60 (coe v0)

-- Haskell.Prim.Foldable._.or
d_or_242 :: T_Foldable_8 -> AgdaAny -> Bool
d_or_242 v0 = coe d_or_62 (coe v0)

-- Haskell.Prim.Foldable._.product
d_product_244 ::
  T_Foldable_8 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Num.T_Num_8 ->
  AgdaAny ->
  AgdaAny
d_product_244 v0 = coe d_product_80 (coe v0)

-- Haskell.Prim.Foldable._.sum
d_sum_246 ::
  T_Foldable_8 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Num.T_Num_8 ->
  AgdaAny ->
  AgdaAny
d_sum_246 v0 = coe d_sum_76 (coe v0)

-- Haskell.Prim.Foldable._.toList
d_toList_248 :: T_Foldable_8 -> () -> AgdaAny -> [AgdaAny]
d_toList_248 v0 = coe d_toList_72 (coe v0)

-- Haskell.Prim.Foldable._.all
d_all_258 ::
  (() -> ()) ->
  T_DefaultFoldable_86 ->
  () ->
  (AgdaAny -> Bool) ->
  AgdaAny ->
  Bool
d_all_258 ~v0 v1 = du_all_258 v1
du_all_258 ::
  T_DefaultFoldable_86 -> () -> (AgdaAny -> Bool) -> AgdaAny -> Bool
du_all_258 v0 v1 = coe du_all_180 (coe v0)

-- Haskell.Prim.Foldable._.and
d_and_260 :: (() -> ()) -> T_DefaultFoldable_86 -> AgdaAny -> Bool
d_and_260 ~v0 v1 = du_and_260 v1
du_and_260 :: T_DefaultFoldable_86 -> AgdaAny -> Bool
du_and_260 v0 = coe du_and_182 (coe v0)

-- Haskell.Prim.Foldable._.any
d_any_262 ::
  (() -> ()) ->
  T_DefaultFoldable_86 ->
  () ->
  (AgdaAny -> Bool) ->
  AgdaAny ->
  Bool
d_any_262 ~v0 v1 = du_any_262 v1
du_any_262 ::
  T_DefaultFoldable_86 -> () -> (AgdaAny -> Bool) -> AgdaAny -> Bool
du_any_262 v0 v1 = coe du_any_178 (coe v0)

-- Haskell.Prim.Foldable._.concat
d_concat_264 ::
  (() -> ()) -> T_DefaultFoldable_86 -> () -> AgdaAny -> [AgdaAny]
d_concat_264 ~v0 v1 = du_concat_264 v1
du_concat_264 :: T_DefaultFoldable_86 -> () -> AgdaAny -> [AgdaAny]
du_concat_264 v0 v1 = coe du_concat_188 (coe v0)

-- Haskell.Prim.Foldable._.concatMap
d_concatMap_266 ::
  (() -> ()) ->
  T_DefaultFoldable_86 ->
  () ->
  () ->
  (AgdaAny -> [AgdaAny]) ->
  AgdaAny ->
  [AgdaAny]
d_concatMap_266 ~v0 v1 = du_concatMap_266 v1
du_concatMap_266 ::
  T_DefaultFoldable_86 ->
  () ->
  () ->
  (AgdaAny -> [AgdaAny]) ->
  AgdaAny ->
  [AgdaAny]
du_concatMap_266 v0 v1 v2 = coe du_concatMap_190 (coe v0)

-- Haskell.Prim.Foldable._.elem
d_elem_268 ::
  (() -> ()) ->
  T_DefaultFoldable_86 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  AgdaAny ->
  AgdaAny ->
  Bool
d_elem_268 ~v0 v1 = du_elem_268 v1
du_elem_268 ::
  T_DefaultFoldable_86 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  AgdaAny ->
  AgdaAny ->
  Bool
du_elem_268 v0 v1 v2 v3 = coe du_elem_192 (coe v0) v2 v3

-- Haskell.Prim.Foldable._.foldMap
d_foldMap_270 ::
  T_DefaultFoldable_86 ->
  () ->
  () ->
  MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d_foldMap_270 v0 = coe d_foldMap_160 (coe v0)

-- Haskell.Prim.Foldable._.foldl
d_foldl_272 ::
  (() -> ()) ->
  T_DefaultFoldable_86 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d_foldl_272 ~v0 v1 = du_foldl_272 v1
du_foldl_272 ::
  T_DefaultFoldable_86 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
du_foldl_272 v0 v1 v2 v3 v4 v5 = coe du_foldl_170 (coe v0) v3 v4 v5

-- Haskell.Prim.Foldable._.foldr
d_foldr_274 ::
  (() -> ()) ->
  T_DefaultFoldable_86 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d_foldr_274 ~v0 v1 = du_foldr_274 v1
du_foldr_274 ::
  T_DefaultFoldable_86 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
du_foldr_274 v0 v1 v2 v3 v4 v5 = coe du_foldr_162 (coe v0) v3 v4 v5

-- Haskell.Prim.Foldable._.length
d_length_276 ::
  (() -> ()) ->
  T_DefaultFoldable_86 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Haskell.Prim.Int.T_Int_6
d_length_276 ~v0 v1 = du_length_276 v1
du_length_276 ::
  T_DefaultFoldable_86 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Haskell.Prim.Int.T_Int_6
du_length_276 v0 v1 = coe du_length_214 (coe v0)

-- Haskell.Prim.Foldable._.notElem
d_notElem_278 ::
  (() -> ()) ->
  T_DefaultFoldable_86 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  AgdaAny ->
  AgdaAny ->
  Bool
d_notElem_278 ~v0 v1 = du_notElem_278 v1
du_notElem_278 ::
  T_DefaultFoldable_86 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  AgdaAny ->
  AgdaAny ->
  Bool
du_notElem_278 v0 v1 v2 v3 v4 =
  coe du_notElem_198 (coe v0) v2 v3 v4

-- Haskell.Prim.Foldable._.null
d_null_280 ::
  (() -> ()) -> T_DefaultFoldable_86 -> () -> AgdaAny -> Bool
d_null_280 ~v0 v1 = du_null_280 v1
du_null_280 :: T_DefaultFoldable_86 -> () -> AgdaAny -> Bool
du_null_280 v0 v1 = coe du_null_186 (coe v0)

-- Haskell.Prim.Foldable._.or
d_or_282 :: (() -> ()) -> T_DefaultFoldable_86 -> AgdaAny -> Bool
d_or_282 ~v0 v1 = du_or_282 v1
du_or_282 :: T_DefaultFoldable_86 -> AgdaAny -> Bool
du_or_282 v0 = coe du_or_184 (coe v0)

-- Haskell.Prim.Foldable._.product
d_product_284 ::
  (() -> ()) ->
  T_DefaultFoldable_86 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Num.T_Num_8 ->
  AgdaAny ->
  AgdaAny
d_product_284 ~v0 v1 = du_product_284 v1
du_product_284 ::
  T_DefaultFoldable_86 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Num.T_Num_8 ->
  AgdaAny ->
  AgdaAny
du_product_284 v0 v1 v2 = coe du_product_212 (coe v0) v2

-- Haskell.Prim.Foldable._.sum
d_sum_286 ::
  (() -> ()) ->
  T_DefaultFoldable_86 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Num.T_Num_8 ->
  AgdaAny ->
  AgdaAny
d_sum_286 ~v0 v1 = du_sum_286 v1
du_sum_286 ::
  T_DefaultFoldable_86 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Num.T_Num_8 ->
  AgdaAny ->
  AgdaAny
du_sum_286 v0 v1 v2 = coe du_sum_208 (coe v0) v2

-- Haskell.Prim.Foldable._.toList
d_toList_288 ::
  (() -> ()) -> T_DefaultFoldable_86 -> () -> AgdaAny -> [AgdaAny]
d_toList_288 ~v0 v1 = du_toList_288 v1
du_toList_288 :: T_DefaultFoldable_86 -> () -> AgdaAny -> [AgdaAny]
du_toList_288 v0 v1 = coe du_toList_204 (coe v0)

-- Haskell.Prim.Foldable._.M.all
d_all_292 ::
  T_Foldable_8 -> () -> (AgdaAny -> Bool) -> AgdaAny -> Bool
d_all_292 v0 = coe d_all_56 (coe v0)

-- Haskell.Prim.Foldable._.M.and
d_and_294 :: T_Foldable_8 -> AgdaAny -> Bool
d_and_294 v0 = coe d_and_58 (coe v0)

-- Haskell.Prim.Foldable._.M.any
d_any_296 ::
  T_Foldable_8 -> () -> (AgdaAny -> Bool) -> AgdaAny -> Bool
d_any_296 v0 = coe d_any_54 (coe v0)

-- Haskell.Prim.Foldable._.M.concat
d_concat_298 :: T_Foldable_8 -> () -> AgdaAny -> [AgdaAny]
d_concat_298 v0 = coe d_concat_64 (coe v0)

-- Haskell.Prim.Foldable._.M.concatMap
d_concatMap_300 ::
  T_Foldable_8 ->
  () ->
  () ->
  (AgdaAny -> [AgdaAny]) ->
  AgdaAny ->
  [AgdaAny]
d_concatMap_300 v0 = coe d_concatMap_66 (coe v0)

-- Haskell.Prim.Foldable._.M.elem
d_elem_302 ::
  T_Foldable_8 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  AgdaAny ->
  AgdaAny ->
  Bool
d_elem_302 v0 = coe d_elem_68 (coe v0)

-- Haskell.Prim.Foldable._.M.foldMap
d_foldMap_304 ::
  T_Foldable_8 ->
  () ->
  () ->
  MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d_foldMap_304 v0 = coe d_foldMap_48 (coe v0)

-- Haskell.Prim.Foldable._.M.foldl
d_foldl_306 ::
  T_Foldable_8 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d_foldl_306 v0 = coe d_foldl_52 (coe v0)

-- Haskell.Prim.Foldable._.M.foldr
d_foldr_308 ::
  T_Foldable_8 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d_foldr_308 v0 = coe d_foldr_50 (coe v0)

-- Haskell.Prim.Foldable._.M.length
d_length_310 ::
  T_Foldable_8 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Haskell.Prim.Int.T_Int_6
d_length_310 v0 = coe d_length_82 (coe v0)

-- Haskell.Prim.Foldable._.M.notElem
d_notElem_312 ::
  T_Foldable_8 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  AgdaAny ->
  AgdaAny ->
  Bool
d_notElem_312 v0 = coe d_notElem_70 (coe v0)

-- Haskell.Prim.Foldable._.M.null
d_null_314 :: T_Foldable_8 -> () -> AgdaAny -> Bool
d_null_314 v0 = coe d_null_60 (coe v0)

-- Haskell.Prim.Foldable._.M.or
d_or_316 :: T_Foldable_8 -> AgdaAny -> Bool
d_or_316 v0 = coe d_or_62 (coe v0)

-- Haskell.Prim.Foldable._.M.product
d_product_318 ::
  T_Foldable_8 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Num.T_Num_8 ->
  AgdaAny ->
  AgdaAny
d_product_318 v0 = coe d_product_80 (coe v0)

-- Haskell.Prim.Foldable._.M.sum
d_sum_320 ::
  T_Foldable_8 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Num.T_Num_8 ->
  AgdaAny ->
  AgdaAny
d_sum_320 v0 = coe d_sum_76 (coe v0)

-- Haskell.Prim.Foldable._.M.toList
d_toList_322 :: T_Foldable_8 -> () -> AgdaAny -> [AgdaAny]
d_toList_322 v0 = coe d_toList_72 (coe v0)

-- Haskell.Prim.Foldable.foldMap=_
d_foldMap'61'__328 ::
  (() -> ()) ->
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  T_Foldable_8
d_foldMap'61'__328 ~v0 v1 = du_foldMap'61'__328 v1
du_foldMap'61'__328 ::
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  T_Foldable_8
du_foldMap'61'__328 v0 =
  coe
    C_Foldable'46'constructor_2791
    (coe v0)
    ( \v1 v2 v3 v4 v5 ->
        coe
          du_foldr_162
          (coe C_DefaultFoldable'46'constructor_4805 (coe v0))
          v3
          v4
          v5
    )
    ( \v1 v2 v3 v4 v5 ->
        coe
          du_foldl_170
          (coe C_DefaultFoldable'46'constructor_4805 (coe v0))
          v3
          v4
          v5
    )
    ( \v1 ->
        coe
          du_any_178
          (coe C_DefaultFoldable'46'constructor_4805 (coe v0))
    )
    ( \v1 ->
        coe
          du_all_180
          (coe C_DefaultFoldable'46'constructor_4805 (coe v0))
    )
    ( coe
        du_and_182
        (coe C_DefaultFoldable'46'constructor_4805 (coe v0))
    )
    ( \v1 ->
        coe
          du_null_186
          (coe C_DefaultFoldable'46'constructor_4805 (coe v0))
    )
    ( coe
        du_or_184
        (coe C_DefaultFoldable'46'constructor_4805 (coe v0))
    )
    ( \v1 ->
        coe
          du_concat_188
          (coe C_DefaultFoldable'46'constructor_4805 (coe v0))
    )
    ( \v1 v2 ->
        coe
          du_concatMap_190
          (coe C_DefaultFoldable'46'constructor_4805 (coe v0))
    )
    ( \v1 v2 v3 ->
        coe
          du_elem_192
          (coe C_DefaultFoldable'46'constructor_4805 (coe v0))
          v2
          v3
    )
    ( \v1 v2 v3 v4 ->
        coe
          du_notElem_198
          (coe C_DefaultFoldable'46'constructor_4805 (coe v0))
          v2
          v3
          v4
    )
    ( \v1 ->
        coe
          du_toList_204
          (coe C_DefaultFoldable'46'constructor_4805 (coe v0))
    )
    ( \v1 v2 ->
        coe
          du_sum_208
          (coe C_DefaultFoldable'46'constructor_4805 (coe v0))
          v2
    )
    ( \v1 v2 ->
        coe
          du_product_212
          (coe C_DefaultFoldable'46'constructor_4805 (coe v0))
          v2
    )
    ( \v1 ->
        coe
          du_length_214
          (coe C_DefaultFoldable'46'constructor_4805 (coe v0))
    )

-- Haskell.Prim.Foldable._.all
d_all_336 ::
  (() -> ()) ->
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  () ->
  (AgdaAny -> Bool) ->
  AgdaAny ->
  Bool
d_all_336 ~v0 v1 = du_all_336 v1
du_all_336 ::
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  () ->
  (AgdaAny -> Bool) ->
  AgdaAny ->
  Bool
du_all_336 v0 v1 =
  coe
    du_all_180
    (coe C_DefaultFoldable'46'constructor_4805 (coe v0))

-- Haskell.Prim.Foldable._.and
d_and_338 ::
  (() -> ()) ->
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  AgdaAny ->
  Bool
d_and_338 ~v0 v1 = du_and_338 v1
du_and_338 ::
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  AgdaAny ->
  Bool
du_and_338 v0 =
  coe
    du_and_182
    (coe C_DefaultFoldable'46'constructor_4805 (coe v0))

-- Haskell.Prim.Foldable._.any
d_any_340 ::
  (() -> ()) ->
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  () ->
  (AgdaAny -> Bool) ->
  AgdaAny ->
  Bool
d_any_340 ~v0 v1 = du_any_340 v1
du_any_340 ::
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  () ->
  (AgdaAny -> Bool) ->
  AgdaAny ->
  Bool
du_any_340 v0 v1 =
  coe
    du_any_178
    (coe C_DefaultFoldable'46'constructor_4805 (coe v0))

-- Haskell.Prim.Foldable._.concat
d_concat_342 ::
  (() -> ()) ->
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  () ->
  AgdaAny ->
  [AgdaAny]
d_concat_342 ~v0 v1 = du_concat_342 v1
du_concat_342 ::
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  () ->
  AgdaAny ->
  [AgdaAny]
du_concat_342 v0 v1 =
  coe
    du_concat_188
    (coe C_DefaultFoldable'46'constructor_4805 (coe v0))

-- Haskell.Prim.Foldable._.concatMap
d_concatMap_344 ::
  (() -> ()) ->
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  () ->
  () ->
  (AgdaAny -> [AgdaAny]) ->
  AgdaAny ->
  [AgdaAny]
d_concatMap_344 ~v0 v1 = du_concatMap_344 v1
du_concatMap_344 ::
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  () ->
  () ->
  (AgdaAny -> [AgdaAny]) ->
  AgdaAny ->
  [AgdaAny]
du_concatMap_344 v0 v1 v2 =
  coe
    du_concatMap_190
    (coe C_DefaultFoldable'46'constructor_4805 (coe v0))

-- Haskell.Prim.Foldable._.elem
d_elem_346 ::
  (() -> ()) ->
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  AgdaAny ->
  AgdaAny ->
  Bool
d_elem_346 ~v0 v1 = du_elem_346 v1
du_elem_346 ::
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  AgdaAny ->
  AgdaAny ->
  Bool
du_elem_346 v0 v1 v2 v3 =
  coe
    du_elem_192
    (coe C_DefaultFoldable'46'constructor_4805 (coe v0))
    v2
    v3

-- Haskell.Prim.Foldable._.foldl
d_foldl_350 ::
  (() -> ()) ->
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d_foldl_350 ~v0 v1 = du_foldl_350 v1
du_foldl_350 ::
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
du_foldl_350 v0 v1 v2 v3 v4 v5 =
  coe
    du_foldl_170
    (coe C_DefaultFoldable'46'constructor_4805 (coe v0))
    v3
    v4
    v5

-- Haskell.Prim.Foldable._.foldr
d_foldr_352 ::
  (() -> ()) ->
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d_foldr_352 ~v0 v1 = du_foldr_352 v1
du_foldr_352 ::
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
du_foldr_352 v0 v1 v2 v3 v4 v5 =
  coe
    du_foldr_162
    (coe C_DefaultFoldable'46'constructor_4805 (coe v0))
    v3
    v4
    v5

-- Haskell.Prim.Foldable._.length
d_length_354 ::
  (() -> ()) ->
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Haskell.Prim.Int.T_Int_6
d_length_354 ~v0 v1 = du_length_354 v1
du_length_354 ::
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Haskell.Prim.Int.T_Int_6
du_length_354 v0 v1 =
  coe
    du_length_214
    (coe C_DefaultFoldable'46'constructor_4805 (coe v0))

-- Haskell.Prim.Foldable._.notElem
d_notElem_356 ::
  (() -> ()) ->
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  AgdaAny ->
  AgdaAny ->
  Bool
d_notElem_356 ~v0 v1 = du_notElem_356 v1
du_notElem_356 ::
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  AgdaAny ->
  AgdaAny ->
  Bool
du_notElem_356 v0 v1 v2 v3 v4 =
  coe
    du_notElem_198
    (coe C_DefaultFoldable'46'constructor_4805 (coe v0))
    v2
    v3
    v4

-- Haskell.Prim.Foldable._.null
d_null_358 ::
  (() -> ()) ->
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  () ->
  AgdaAny ->
  Bool
d_null_358 ~v0 v1 = du_null_358 v1
du_null_358 ::
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  () ->
  AgdaAny ->
  Bool
du_null_358 v0 v1 =
  coe
    du_null_186
    (coe C_DefaultFoldable'46'constructor_4805 (coe v0))

-- Haskell.Prim.Foldable._.or
d_or_360 ::
  (() -> ()) ->
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  AgdaAny ->
  Bool
d_or_360 ~v0 v1 = du_or_360 v1
du_or_360 ::
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  AgdaAny ->
  Bool
du_or_360 v0 =
  coe
    du_or_184
    (coe C_DefaultFoldable'46'constructor_4805 (coe v0))

-- Haskell.Prim.Foldable._.product
d_product_362 ::
  (() -> ()) ->
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  () ->
  MAlonzo.Code.Haskell.Prim.Num.T_Num_8 ->
  AgdaAny ->
  AgdaAny
d_product_362 ~v0 v1 = du_product_362 v1
du_product_362 ::
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  () ->
  MAlonzo.Code.Haskell.Prim.Num.T_Num_8 ->
  AgdaAny ->
  AgdaAny
du_product_362 v0 v1 v2 =
  coe
    du_product_212
    (coe C_DefaultFoldable'46'constructor_4805 (coe v0))
    v2

-- Haskell.Prim.Foldable._.sum
d_sum_364 ::
  (() -> ()) ->
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  () ->
  MAlonzo.Code.Haskell.Prim.Num.T_Num_8 ->
  AgdaAny ->
  AgdaAny
d_sum_364 ~v0 v1 = du_sum_364 v1
du_sum_364 ::
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  () ->
  MAlonzo.Code.Haskell.Prim.Num.T_Num_8 ->
  AgdaAny ->
  AgdaAny
du_sum_364 v0 v1 v2 =
  coe
    du_sum_208
    (coe C_DefaultFoldable'46'constructor_4805 (coe v0))
    v2

-- Haskell.Prim.Foldable._.toList
d_toList_366 ::
  (() -> ()) ->
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  () ->
  AgdaAny ->
  [AgdaAny]
d_toList_366 ~v0 v1 = du_toList_366 v1
du_toList_366 ::
  ( () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  () ->
  AgdaAny ->
  [AgdaAny]
du_toList_366 v0 v1 =
  coe
    du_toList_204
    (coe C_DefaultFoldable'46'constructor_4805 (coe v0))

-- Haskell.Prim.Foldable._.M.all
d_all_370 ::
  T_Foldable_8 -> () -> (AgdaAny -> Bool) -> AgdaAny -> Bool
d_all_370 v0 = coe d_all_56 (coe v0)

-- Haskell.Prim.Foldable._.M.and
d_and_372 :: T_Foldable_8 -> AgdaAny -> Bool
d_and_372 v0 = coe d_and_58 (coe v0)

-- Haskell.Prim.Foldable._.M.any
d_any_374 ::
  T_Foldable_8 -> () -> (AgdaAny -> Bool) -> AgdaAny -> Bool
d_any_374 v0 = coe d_any_54 (coe v0)

-- Haskell.Prim.Foldable._.M.concat
d_concat_376 :: T_Foldable_8 -> () -> AgdaAny -> [AgdaAny]
d_concat_376 v0 = coe d_concat_64 (coe v0)

-- Haskell.Prim.Foldable._.M.concatMap
d_concatMap_378 ::
  T_Foldable_8 ->
  () ->
  () ->
  (AgdaAny -> [AgdaAny]) ->
  AgdaAny ->
  [AgdaAny]
d_concatMap_378 v0 = coe d_concatMap_66 (coe v0)

-- Haskell.Prim.Foldable._.M.elem
d_elem_380 ::
  T_Foldable_8 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  AgdaAny ->
  AgdaAny ->
  Bool
d_elem_380 v0 = coe d_elem_68 (coe v0)

-- Haskell.Prim.Foldable._.M.foldMap
d_foldMap_382 ::
  T_Foldable_8 ->
  () ->
  () ->
  MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d_foldMap_382 v0 = coe d_foldMap_48 (coe v0)

-- Haskell.Prim.Foldable._.M.foldl
d_foldl_384 ::
  T_Foldable_8 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d_foldl_384 v0 = coe d_foldl_52 (coe v0)

-- Haskell.Prim.Foldable._.M.foldr
d_foldr_386 ::
  T_Foldable_8 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d_foldr_386 v0 = coe d_foldr_50 (coe v0)

-- Haskell.Prim.Foldable._.M.length
d_length_388 ::
  T_Foldable_8 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Haskell.Prim.Int.T_Int_6
d_length_388 v0 = coe d_length_82 (coe v0)

-- Haskell.Prim.Foldable._.M.notElem
d_notElem_390 ::
  T_Foldable_8 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  AgdaAny ->
  AgdaAny ->
  Bool
d_notElem_390 v0 = coe d_notElem_70 (coe v0)

-- Haskell.Prim.Foldable._.M.null
d_null_392 :: T_Foldable_8 -> () -> AgdaAny -> Bool
d_null_392 v0 = coe d_null_60 (coe v0)

-- Haskell.Prim.Foldable._.M.or
d_or_394 :: T_Foldable_8 -> AgdaAny -> Bool
d_or_394 v0 = coe d_or_62 (coe v0)

-- Haskell.Prim.Foldable._.M.product
d_product_396 ::
  T_Foldable_8 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Num.T_Num_8 ->
  AgdaAny ->
  AgdaAny
d_product_396 v0 = coe d_product_80 (coe v0)

-- Haskell.Prim.Foldable._.M.sum
d_sum_398 ::
  T_Foldable_8 ->
  () ->
  MAlonzo.Code.Haskell.Prim.Num.T_Num_8 ->
  AgdaAny ->
  AgdaAny
d_sum_398 v0 = coe d_sum_76 (coe v0)

-- Haskell.Prim.Foldable._.M.toList
d_toList_400 :: T_Foldable_8 -> () -> AgdaAny -> [AgdaAny]
d_toList_400 v0 = coe d_toList_72 (coe v0)

-- Haskell.Prim.Foldable.iFoldableList
d_iFoldableList_402 :: T_Foldable_8
d_iFoldableList_402 =
  coe
    du_foldMap'61'__328
    (\v0 v1 v2 v3 v4 -> coe du_foldMapList_408 v2 v3 v4)

-- Haskell.Prim.Foldable._.foldMapList
d_foldMapList_408 ::
  () ->
  () ->
  MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  AgdaAny
d_foldMapList_408 ~v0 ~v1 v2 v3 v4 = du_foldMapList_408 v2 v3 v4
du_foldMapList_408 ::
  MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  AgdaAny
du_foldMapList_408 v0 v1 v2 =
  case coe v2 of
    [] -> coe MAlonzo.Code.Haskell.Prim.Monoid.d_mempty_86 (coe v0)
    (:) v3 v4 ->
      coe
        MAlonzo.Code.Haskell.Prim.Monoid.d__'60''62'__14
        (MAlonzo.Code.Haskell.Prim.Monoid.d_super_88 (coe v0))
        (coe v1 v3)
        (coe du_foldMapList_408 (coe v0) (coe v1) (coe v4))
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Foldable.iFoldableMaybe
d_iFoldableMaybe_418 :: T_Foldable_8
d_iFoldableMaybe_418 =
  coe
    du_foldMap'61'__328
    ( coe
        ( \v0 v1 v2 v3 v4 ->
            case coe v4 of
              MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16 ->
                coe MAlonzo.Code.Haskell.Prim.Monoid.d_mempty_86 (coe v2)
              MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 v5 -> coe v3 v5
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )

-- Haskell.Prim.Foldable.iFoldableEither
d_iFoldableEither_426 :: () -> T_Foldable_8
d_iFoldableEither_426 ~v0 = du_iFoldableEither_426
du_iFoldableEither_426 :: T_Foldable_8
du_iFoldableEither_426 =
  coe
    du_foldMap'61'__328
    ( coe
        ( \v0 v1 v2 v3 v4 ->
            case coe v4 of
              MAlonzo.Code.Haskell.Prim.Either.C_Left_16 v5 ->
                coe MAlonzo.Code.Haskell.Prim.Monoid.d_mempty_86 (coe v2)
              MAlonzo.Code.Haskell.Prim.Either.C_Right_18 v5 -> coe v3 v5
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )

-- Haskell.Prim.Foldable.iFoldablePair
d_iFoldablePair_436 :: () -> T_Foldable_8
d_iFoldablePair_436 ~v0 = du_iFoldablePair_436
du_iFoldablePair_436 :: T_Foldable_8
du_iFoldablePair_436 =
  coe
    du_foldMap'61'__328
    ( coe
        ( \v0 v1 v2 v3 v4 ->
            coe v3 (MAlonzo.Code.Haskell.Prim.Tuple.d_snd_22 (coe v4))
        )
    )
