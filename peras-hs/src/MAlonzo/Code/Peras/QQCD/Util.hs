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

module MAlonzo.Code.Peras.QQCD.Util where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Haskell.Prim
import qualified MAlonzo.Code.Haskell.Prim.Applicative
import qualified MAlonzo.Code.Haskell.Prim.Bool
import qualified MAlonzo.Code.Haskell.Prim.Eq
import qualified MAlonzo.Code.Haskell.Prim.Foldable
import qualified MAlonzo.Code.Haskell.Prim.Functor
import qualified MAlonzo.Code.Haskell.Prim.List
import qualified MAlonzo.Code.Haskell.Prim.Ord
import qualified MAlonzo.Code.Haskell.Prim.Tuple
import qualified MAlonzo.Code.Peras.QQCD.Crypto
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

-- Peras.QCD.Util.eqBy
d_eqBy_8 ::
  () ->
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  Bool
d_eqBy_8 ~v0 ~v1 v2 v3 v4 v5 = du_eqBy_8 v2 v3 v4 v5
du_eqBy_8 ::
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  Bool
du_eqBy_8 v0 v1 v2 v3 =
  coe
    MAlonzo.Code.Haskell.Prim.Eq.d__'61''61'__14
    v0
    (coe v1 v2)
    (coe v1 v3)

-- Peras.QCD.Util.eqByBS
d_eqByBS_16 ::
  () ->
  (AgdaAny -> MAlonzo.Code.Peras.QQCD.Crypto.T_ByteString_6) ->
  AgdaAny ->
  AgdaAny ->
  Bool
d_eqByBS_16 ~v0 v1 v2 v3 = du_eqByBS_16 v1 v2 v3
du_eqByBS_16 ::
  (AgdaAny -> MAlonzo.Code.Peras.QQCD.Crypto.T_ByteString_6) ->
  AgdaAny ->
  AgdaAny ->
  Bool
du_eqByBS_16 v0 v1 v2 =
  coe
    MAlonzo.Code.Peras.QQCD.Crypto.d_eqBS_12
    (coe v0 v1)
    (coe v0 v2)

-- Peras.QCD.Util._⇉_
d__'8649'__26 ::
  (() -> ()) ->
  () ->
  () ->
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
d__'8649'__26 ~v0 ~v1 ~v2 v3 v4 v5 = du__'8649'__26 v3 v4 v5
du__'8649'__26 ::
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
du__'8649'__26 v0 v1 v2 =
  coe
    MAlonzo.Code.Haskell.Prim.Functor.d_fmap_24
    v0
    erased
    erased
    v2
    v1

-- Peras.QCD.Util.addOne
d_addOne_32 :: Integer -> Integer
d_addOne_32 v0 = coe addInt (coe (1 :: Integer)) (coe v0)

-- Peras.QCD.Util.checkDescending
d_checkDescending_36 ::
  () ->
  ( AgdaAny ->
    AgdaAny ->
    MAlonzo.Code.Haskell.Prim.Ord.T_Ordering_6
  ) ->
  [AgdaAny] ->
  Bool
d_checkDescending_36 ~v0 v1 v2 = du_checkDescending_36 v1 v2
du_checkDescending_36 ::
  ( AgdaAny ->
    AgdaAny ->
    MAlonzo.Code.Haskell.Prim.Ord.T_Ordering_6
  ) ->
  [AgdaAny] ->
  Bool
du_checkDescending_36 v0 v1 =
  case coe v1 of
    [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
    (:) v2 v3 ->
      case coe v3 of
        [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
        (:) v4 v5 ->
          coe
            MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
            ( coe
                MAlonzo.Code.Haskell.Prim.Eq.d__'61''61'__14
                MAlonzo.Code.Haskell.Prim.Ord.d_iEqOrdering_14
                (coe v0 v2 v4)
                (coe MAlonzo.Code.Haskell.Prim.Ord.C_GT_12)
            )
            (coe du_checkDescending_36 (coe v0) (coe v3))
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Util.insertDescending
d_insertDescending_46 ::
  () ->
  ( AgdaAny ->
    AgdaAny ->
    MAlonzo.Code.Haskell.Prim.Ord.T_Ordering_6
  ) ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny]
d_insertDescending_46 ~v0 v1 v2 v3 =
  du_insertDescending_46 v1 v2 v3
du_insertDescending_46 ::
  ( AgdaAny ->
    AgdaAny ->
    MAlonzo.Code.Haskell.Prim.Ord.T_Ordering_6
  ) ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny]
du_insertDescending_46 v0 v1 v2 =
  case coe v2 of
    [] ->
      coe
        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
        (coe v1)
        (coe v2)
    (:) v3 v4 ->
      coe
        MAlonzo.Code.Haskell.Prim.du_case_of__58
        (coe v0 v1 v3)
        ( \v5 v6 ->
            coe
              du_'46'extendedlambda0_58
              (coe v0)
              (coe v1)
              (coe v3)
              (coe v4)
              v5
        )
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Util..extendedlambda0
d_'46'extendedlambda0_58 ::
  () ->
  ( AgdaAny ->
    AgdaAny ->
    MAlonzo.Code.Haskell.Prim.Ord.T_Ordering_6
  ) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ordering_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [AgdaAny]
d_'46'extendedlambda0_58 ~v0 v1 v2 v3 v4 v5 ~v6 =
  du_'46'extendedlambda0_58 v1 v2 v3 v4 v5
du_'46'extendedlambda0_58 ::
  ( AgdaAny ->
    AgdaAny ->
    MAlonzo.Code.Haskell.Prim.Ord.T_Ordering_6
  ) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ordering_6 ->
  [AgdaAny]
du_'46'extendedlambda0_58 v0 v1 v2 v3 v4 =
  case coe v4 of
    MAlonzo.Code.Haskell.Prim.Ord.C_LT_8 ->
      coe
        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
        (coe v2)
        (coe du_insertDescending_46 (coe v0) (coe v1) (coe v3))
    MAlonzo.Code.Haskell.Prim.Ord.C_EQ_10 ->
      coe
        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
        (coe v2)
        (coe v3)
    MAlonzo.Code.Haskell.Prim.Ord.C_GT_12 ->
      coe
        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
        (coe v1)
        ( coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe v2)
            (coe v3)
        )
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Util.unionDescending
d_unionDescending_62 ::
  () ->
  () ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny]
d_unionDescending_62 ~v0 ~v1 v2 v3 v4 v5 =
  du_unionDescending_62 v2 v3 v4 v5
du_unionDescending_62 ::
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny]
du_unionDescending_62 v0 v1 v2 v3 =
  coe
    MAlonzo.Code.Haskell.Prim.Foldable.du_foldr_162
    ( coe
        MAlonzo.Code.Haskell.Prim.Foldable.C_DefaultFoldable'46'constructor_4805
        ( \v4 v5 v6 v7 v8 ->
            coe
              MAlonzo.Code.Haskell.Prim.Foldable.du_foldMapList_408
              v6
              v7
              v8
        )
    )
    ( coe
        du_insertDescending_46
        ( coe
            ( \v4 v5 ->
                coe
                  MAlonzo.Code.Haskell.Prim.Ord.d_compare_56
                  v0
                  (coe v1 v4)
                  (coe v1 v5)
            )
        )
    )
    (coe v3)
    (coe v2)

-- Peras.QCD.Util.groupBy
d_groupBy_74 ::
  () -> (AgdaAny -> AgdaAny -> Bool) -> [AgdaAny] -> [[AgdaAny]]
d_groupBy_74 ~v0 v1 v2 = du_groupBy_74 v1 v2
du_groupBy_74 ::
  (AgdaAny -> AgdaAny -> Bool) -> [AgdaAny] -> [[AgdaAny]]
du_groupBy_74 v0 v1 =
  case coe v1 of
    [] -> coe v1
    (:) v2 v3 ->
      coe
        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
        ( coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe v2)
            ( coe
                MAlonzo.Code.Haskell.Prim.Tuple.d_fst_20
                ( coe
                    MAlonzo.Code.Haskell.Prim.List.du_span_124
                    (coe v0 v2)
                    (coe v3)
                )
            )
        )
        ( coe
            du_groupBy_74
            (coe v0)
            ( coe
                MAlonzo.Code.Haskell.Prim.Tuple.d_snd_22
                ( coe
                    MAlonzo.Code.Haskell.Prim.List.du_span_124
                    (coe v0 v2)
                    (coe v3)
                )
            )
        )
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Util.count
d_count_86 :: () -> [AgdaAny] -> Integer
d_count_86 ~v0 ~v1 = du_count_86
du_count_86 :: Integer
du_count_86 = coe (0 :: Integer)

-- Peras.QCD.Util.firstWithDefault
d_firstWithDefault_88 :: () -> AgdaAny -> [AgdaAny] -> AgdaAny
d_firstWithDefault_88 ~v0 v1 v2 = du_firstWithDefault_88 v1 v2
du_firstWithDefault_88 :: AgdaAny -> [AgdaAny] -> AgdaAny
du_firstWithDefault_88 v0 v1 =
  case coe v1 of
    [] -> coe v0
    (:) v2 v3 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Util._↞_
d__'8606'__96 ::
  (() -> ()) ->
  () ->
  MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d__'8606'__96 ~v0 ~v1 v2 v3 v4 = du__'8606'__96 v2 v3 v4
du__'8606'__96 ::
  MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
du__'8606'__96 v0 v1 v2 =
  coe
    MAlonzo.Code.Haskell.Prim.Functor.d_fmap_24
    (MAlonzo.Code.Haskell.Prim.Applicative.d_super_26 (coe v0))
    erased
    erased
    ( \v3 ->
        coe
          MAlonzo.Code.Haskell.Prim.List.du__'43''43'__20
          (coe v3)
          ( coe
              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
              (coe v2)
              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
          )
    )
    v1

-- Peras.QCD.Util.divideNat
d_divideNat_104 :: Integer -> Integer -> Integer
d_divideNat_104 v0 v1 =
  coe d_go_114 (coe v0) (coe v1) (coe (0 :: Integer))

-- Peras.QCD.Util._.go
d_go_114 :: Integer -> Integer -> Integer -> Integer
d_go_114 v0 v1 v2 =
  coe
    MAlonzo.Code.Haskell.Prim.du_if_then_else__68
    ( coe
        MAlonzo.Code.Haskell.Prim.Ord.d__'60'__58
        MAlonzo.Code.Haskell.Prim.Ord.d_iOrdNat_246
        v0
        (mulInt (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v1))
    )
    (coe (\v3 -> v2))
    ( coe
        ( \v3 ->
            d_go_114
              (coe v0)
              (coe v1)
              (coe addInt (coe (1 :: Integer)) (coe v2))
        )
    )
