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

module MAlonzo.Code.Haskell.Prim.Monoid where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Haskell.Prim
import qualified MAlonzo.Code.Haskell.Prim.Bool
import qualified MAlonzo.Code.Haskell.Prim.Either
import qualified MAlonzo.Code.Haskell.Prim.List
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

-- Haskell.Prim.Monoid.Semigroup
d_Semigroup_8 a0 = ()
newtype T_Semigroup_8
  = C_Semigroup'46'constructor_7 (AgdaAny -> AgdaAny -> AgdaAny)

-- Haskell.Prim.Monoid.Semigroup._<>_
d__'60''62'__14 :: T_Semigroup_8 -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''62'__14 v0 =
  case coe v0 of
    C_Semigroup'46'constructor_7 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Monoid._._<>_
d__'60''62'__18 :: T_Semigroup_8 -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''62'__18 v0 = coe d__'60''62'__14 (coe v0)

-- Haskell.Prim.Monoid.iSemigroupList
d_iSemigroupList_20 :: () -> T_Semigroup_8
d_iSemigroupList_20 ~v0 = du_iSemigroupList_20
du_iSemigroupList_20 :: T_Semigroup_8
du_iSemigroupList_20 =
  coe
    C_Semigroup'46'constructor_7
    (coe MAlonzo.Code.Haskell.Prim.List.du__'43''43'__20)

-- Haskell.Prim.Monoid.iSemigroupMaybe
d_iSemigroupMaybe_22 :: () -> T_Semigroup_8 -> T_Semigroup_8
d_iSemigroupMaybe_22 ~v0 v1 = du_iSemigroupMaybe_22 v1
du_iSemigroupMaybe_22 :: T_Semigroup_8 -> T_Semigroup_8
du_iSemigroupMaybe_22 v0 =
  coe
    C_Semigroup'46'constructor_7
    ( coe
        ( \v1 ->
            case coe v1 of
              MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16 -> coe (\v2 -> v2)
              MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 v2 ->
                coe
                  ( \v3 ->
                      case coe v3 of
                        MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16 -> coe v1
                        MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 v4 ->
                          coe
                            MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18
                            (coe d__'60''62'__14 v0 v2 v4)
                        _ -> MAlonzo.RTE.mazUnreachableError
                  )
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )

-- Haskell.Prim.Monoid.iSemigroupEither
d_iSemigroupEither_32 :: () -> () -> T_Semigroup_8
d_iSemigroupEither_32 ~v0 ~v1 = du_iSemigroupEither_32
du_iSemigroupEither_32 :: T_Semigroup_8
du_iSemigroupEither_32 =
  coe
    C_Semigroup'46'constructor_7
    ( coe
        ( \v0 ->
            let v1 = \v1 -> v0
             in coe
                  ( case coe v0 of
                      MAlonzo.Code.Haskell.Prim.Either.C_Left_16 v2 -> coe (\v3 -> v3)
                      _ -> coe v1
                  )
        )
    )

-- Haskell.Prim.Monoid.iSemigroupFun
d_iSemigroupFun_38 :: () -> () -> T_Semigroup_8 -> T_Semigroup_8
d_iSemigroupFun_38 ~v0 ~v1 v2 = du_iSemigroupFun_38 v2
du_iSemigroupFun_38 :: T_Semigroup_8 -> T_Semigroup_8
du_iSemigroupFun_38 v0 =
  coe
    C_Semigroup'46'constructor_7
    ( coe
        (\v1 v2 v3 -> coe d__'60''62'__14 v0 (coe v1 v3) (coe v2 v3))
    )

-- Haskell.Prim.Monoid.iSemigroupUnit
d_iSemigroupUnit_46 :: T_Semigroup_8
d_iSemigroupUnit_46 =
  coe
    C_Semigroup'46'constructor_7
    (coe (\v0 v1 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))

-- Haskell.Prim.Monoid.iSemigroupTuple₂
d_iSemigroupTuple'8322'_48 ::
  () -> () -> T_Semigroup_8 -> T_Semigroup_8 -> T_Semigroup_8
d_iSemigroupTuple'8322'_48 ~v0 ~v1 v2 v3 =
  du_iSemigroupTuple'8322'_48 v2 v3
du_iSemigroupTuple'8322'_48 ::
  T_Semigroup_8 -> T_Semigroup_8 -> T_Semigroup_8
du_iSemigroupTuple'8322'_48 v0 v1 =
  coe
    C_Semigroup'46'constructor_7
    ( coe
        ( \v2 ->
            case coe v2 of
              MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24 v3 v4 ->
                coe
                  ( \v5 ->
                      case coe v5 of
                        MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24 v6 v7 ->
                          coe
                            MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24
                            (coe d__'60''62'__14 v0 v3 v6)
                            (coe d__'60''62'__14 v1 v4 v7)
                        _ -> MAlonzo.RTE.mazUnreachableError
                  )
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )

-- Haskell.Prim.Monoid.iSemigroupTuple₃
d_iSemigroupTuple'8323'_58 ::
  () ->
  () ->
  () ->
  T_Semigroup_8 ->
  T_Semigroup_8 ->
  T_Semigroup_8 ->
  T_Semigroup_8
d_iSemigroupTuple'8323'_58 ~v0 ~v1 ~v2 v3 v4 v5 =
  du_iSemigroupTuple'8323'_58 v3 v4 v5
du_iSemigroupTuple'8323'_58 ::
  T_Semigroup_8 -> T_Semigroup_8 -> T_Semigroup_8 -> T_Semigroup_8
du_iSemigroupTuple'8323'_58 v0 v1 v2 =
  coe
    C_Semigroup'46'constructor_7
    ( coe
        ( \v3 ->
            case coe v3 of
              MAlonzo.Code.Haskell.Prim.Tuple.C__'44'_'44'__40 v4 v5 v6 ->
                coe
                  ( \v7 ->
                      case coe v7 of
                        MAlonzo.Code.Haskell.Prim.Tuple.C__'44'_'44'__40 v8 v9 v10 ->
                          coe
                            MAlonzo.Code.Haskell.Prim.Tuple.C__'44'_'44'__40
                            (coe d__'60''62'__14 v0 v4 v8)
                            (coe d__'60''62'__14 v1 v5 v9)
                            (coe d__'60''62'__14 v2 v6 v10)
                        _ -> MAlonzo.RTE.mazUnreachableError
                  )
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )

-- Haskell.Prim.Monoid.Monoid
d_Monoid_74 a0 = ()
data T_Monoid_74
  = C_Monoid'46'constructor_4387
      AgdaAny
      T_Semigroup_8
      (AgdaAny -> AgdaAny -> AgdaAny)
      ([AgdaAny] -> AgdaAny)

-- Haskell.Prim.Monoid.Monoid.mempty
d_mempty_86 :: T_Monoid_74 -> AgdaAny
d_mempty_86 v0 =
  case coe v0 of
    C_Monoid'46'constructor_4387 v1 v2 v3 v4 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Monoid.Monoid.super
d_super_88 :: T_Monoid_74 -> T_Semigroup_8
d_super_88 v0 =
  case coe v0 of
    C_Monoid'46'constructor_4387 v1 v2 v3 v4 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Monoid.Monoid.mappend
d_mappend_90 :: T_Monoid_74 -> AgdaAny -> AgdaAny -> AgdaAny
d_mappend_90 v0 =
  case coe v0 of
    C_Monoid'46'constructor_4387 v1 v2 v3 v4 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Monoid.Monoid.mconcat
d_mconcat_92 :: T_Monoid_74 -> [AgdaAny] -> AgdaAny
d_mconcat_92 v0 =
  case coe v0 of
    C_Monoid'46'constructor_4387 v1 v2 v3 v4 -> coe v4
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Monoid.DefaultMonoid
d_DefaultMonoid_96 a0 = ()
data T_DefaultMonoid_96
  = C_DefaultMonoid'46'constructor_4503 AgdaAny T_Semigroup_8

-- Haskell.Prim.Monoid.DefaultMonoid.mempty
d_mempty_104 :: T_DefaultMonoid_96 -> AgdaAny
d_mempty_104 v0 =
  case coe v0 of
    C_DefaultMonoid'46'constructor_4503 v1 v2 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Monoid.DefaultMonoid.super
d_super_106 :: T_DefaultMonoid_96 -> T_Semigroup_8
d_super_106 v0 =
  case coe v0 of
    C_DefaultMonoid'46'constructor_4503 v1 v2 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Monoid.DefaultMonoid.mappend
d_mappend_108 ::
  () -> T_DefaultMonoid_96 -> AgdaAny -> AgdaAny -> AgdaAny
d_mappend_108 ~v0 v1 = du_mappend_108 v1
du_mappend_108 ::
  T_DefaultMonoid_96 -> AgdaAny -> AgdaAny -> AgdaAny
du_mappend_108 v0 = coe d__'60''62'__14 (coe d_super_106 (coe v0))

-- Haskell.Prim.Monoid.DefaultMonoid.mconcat
d_mconcat_110 :: () -> T_DefaultMonoid_96 -> [AgdaAny] -> AgdaAny
d_mconcat_110 ~v0 v1 v2 = du_mconcat_110 v1 v2
du_mconcat_110 :: T_DefaultMonoid_96 -> [AgdaAny] -> AgdaAny
du_mconcat_110 v0 v1 =
  case coe v1 of
    [] -> coe d_mempty_104 (coe v0)
    (:) v2 v3 ->
      coe
        d__'60''62'__14
        (d_super_106 (coe v0))
        v2
        (coe du_mconcat_110 (coe v0) (coe v3))
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Monoid._.mappend
d_mappend_118 :: T_Monoid_74 -> AgdaAny -> AgdaAny -> AgdaAny
d_mappend_118 v0 = coe d_mappend_90 (coe v0)

-- Haskell.Prim.Monoid._.mconcat
d_mconcat_120 :: T_Monoid_74 -> [AgdaAny] -> AgdaAny
d_mconcat_120 v0 = coe d_mconcat_92 (coe v0)

-- Haskell.Prim.Monoid._.mempty
d_mempty_122 :: T_Monoid_74 -> AgdaAny
d_mempty_122 v0 = coe d_mempty_86 (coe v0)

-- Haskell.Prim.Monoid._.super
d_super_124 :: T_Monoid_74 -> T_Semigroup_8
d_super_124 v0 = coe d_super_88 (coe v0)

-- Haskell.Prim.Monoid.mempty=_
d_mempty'61'__126 :: () -> T_Semigroup_8 -> AgdaAny -> T_Monoid_74
d_mempty'61'__126 ~v0 v1 v2 = du_mempty'61'__126 v1 v2
du_mempty'61'__126 :: T_Semigroup_8 -> AgdaAny -> T_Monoid_74
du_mempty'61'__126 v0 v1 =
  coe
    C_Monoid'46'constructor_4387
    (coe v1)
    (coe v0)
    ( coe
        du_mappend_108
        (coe C_DefaultMonoid'46'constructor_4503 (coe v1) (coe v0))
    )
    ( coe
        du_mconcat_110
        (coe C_DefaultMonoid'46'constructor_4503 (coe v1) (coe v0))
    )

-- Haskell.Prim.Monoid._.mappend
d_mappend_134 ::
  () -> T_Semigroup_8 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mappend_134 ~v0 v1 v2 = du_mappend_134 v1 v2
du_mappend_134 ::
  T_Semigroup_8 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_mappend_134 v0 v1 =
  coe
    du_mappend_108
    (coe C_DefaultMonoid'46'constructor_4503 (coe v1) (coe v0))

-- Haskell.Prim.Monoid._.mconcat
d_mconcat_136 ::
  () -> T_Semigroup_8 -> AgdaAny -> [AgdaAny] -> AgdaAny
d_mconcat_136 ~v0 v1 v2 = du_mconcat_136 v1 v2
du_mconcat_136 :: T_Semigroup_8 -> AgdaAny -> [AgdaAny] -> AgdaAny
du_mconcat_136 v0 v1 =
  coe
    du_mconcat_110
    (coe C_DefaultMonoid'46'constructor_4503 (coe v1) (coe v0))

-- Haskell.Prim.Monoid.mkMonoid
d_mkMonoid_142 :: () -> T_DefaultMonoid_96 -> T_Monoid_74
d_mkMonoid_142 ~v0 v1 = du_mkMonoid_142 v1
du_mkMonoid_142 :: T_DefaultMonoid_96 -> T_Monoid_74
du_mkMonoid_142 v0 =
  coe
    C_Monoid'46'constructor_4387
    (coe d_mempty_104 (coe v0))
    (coe d_super_106 (coe v0))
    (coe du_mappend_108 (coe v0))
    (coe du_mconcat_110 (coe v0))

-- Haskell.Prim.Monoid._.mappend
d_mappend_150 ::
  () -> T_DefaultMonoid_96 -> AgdaAny -> AgdaAny -> AgdaAny
d_mappend_150 ~v0 v1 = du_mappend_150 v1
du_mappend_150 ::
  T_DefaultMonoid_96 -> AgdaAny -> AgdaAny -> AgdaAny
du_mappend_150 v0 = coe du_mappend_108 (coe v0)

-- Haskell.Prim.Monoid._.mconcat
d_mconcat_152 :: () -> T_DefaultMonoid_96 -> [AgdaAny] -> AgdaAny
d_mconcat_152 ~v0 v1 = du_mconcat_152 v1
du_mconcat_152 :: T_DefaultMonoid_96 -> [AgdaAny] -> AgdaAny
du_mconcat_152 v0 = coe du_mconcat_110 (coe v0)

-- Haskell.Prim.Monoid._.mempty
d_mempty_154 :: T_DefaultMonoid_96 -> AgdaAny
d_mempty_154 v0 = coe d_mempty_104 (coe v0)

-- Haskell.Prim.Monoid._.super
d_super_156 :: T_DefaultMonoid_96 -> T_Semigroup_8
d_super_156 v0 = coe d_super_106 (coe v0)

-- Haskell.Prim.Monoid.iMonoidList
d_iMonoidList_158 :: () -> T_Monoid_74
d_iMonoidList_158 ~v0 = du_iMonoidList_158
du_iMonoidList_158 :: T_Monoid_74
du_iMonoidList_158 =
  coe
    du_mempty'61'__126
    (coe du_iSemigroupList_20)
    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)

-- Haskell.Prim.Monoid.iMonoidMaybe
d_iMonoidMaybe_160 :: () -> T_Semigroup_8 -> T_Monoid_74
d_iMonoidMaybe_160 ~v0 v1 = du_iMonoidMaybe_160 v1
du_iMonoidMaybe_160 :: T_Semigroup_8 -> T_Monoid_74
du_iMonoidMaybe_160 v0 =
  coe
    du_mempty'61'__126
    (coe du_iSemigroupMaybe_22 (coe v0))
    (coe MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16)

-- Haskell.Prim.Monoid.iMonoidFun
d_iMonoidFun_162 :: () -> () -> T_Monoid_74 -> T_Monoid_74
d_iMonoidFun_162 ~v0 ~v1 v2 = du_iMonoidFun_162 v2
du_iMonoidFun_162 :: T_Monoid_74 -> T_Monoid_74
du_iMonoidFun_162 v0 =
  coe
    du_mempty'61'__126
    (coe du_iSemigroupFun_38 (coe d_super_88 (coe v0)))
    (coe (\v1 -> d_mempty_86 (coe v0)))

-- Haskell.Prim.Monoid.iMonoidUnit
d_iMonoidUnit_166 :: T_Monoid_74
d_iMonoidUnit_166 =
  coe
    du_mempty'61'__126
    ( coe
        C_Semigroup'46'constructor_7
        (coe (\v0 v1 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
    )
    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)

-- Haskell.Prim.Monoid.iMonoidTuple₂
d_iMonoidTuple'8322'_168 ::
  () -> () -> T_Monoid_74 -> T_Monoid_74 -> T_Monoid_74
d_iMonoidTuple'8322'_168 ~v0 ~v1 v2 v3 =
  du_iMonoidTuple'8322'_168 v2 v3
du_iMonoidTuple'8322'_168 ::
  T_Monoid_74 -> T_Monoid_74 -> T_Monoid_74
du_iMonoidTuple'8322'_168 v0 v1 =
  coe
    du_mempty'61'__126
    ( coe
        du_iSemigroupTuple'8322'_48
        (coe d_super_88 (coe v0))
        (coe d_super_88 (coe v1))
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24
        (coe d_mempty_86 (coe v0))
        (coe d_mempty_86 (coe v1))
    )

-- Haskell.Prim.Monoid.iMonoidTuple₃
d_iMonoidTuple'8323'_170 ::
  () ->
  () ->
  () ->
  T_Monoid_74 ->
  T_Monoid_74 ->
  T_Monoid_74 ->
  T_Monoid_74
d_iMonoidTuple'8323'_170 ~v0 ~v1 ~v2 v3 v4 v5 =
  du_iMonoidTuple'8323'_170 v3 v4 v5
du_iMonoidTuple'8323'_170 ::
  T_Monoid_74 -> T_Monoid_74 -> T_Monoid_74 -> T_Monoid_74
du_iMonoidTuple'8323'_170 v0 v1 v2 =
  coe
    du_mempty'61'__126
    ( coe
        du_iSemigroupTuple'8323'_58
        (coe d_super_88 (coe v0))
        (coe d_super_88 (coe v1))
        (coe d_super_88 (coe v2))
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.Tuple.C__'44'_'44'__40
        (coe d_mempty_86 (coe v0))
        (coe d_mempty_86 (coe v1))
        (coe d_mempty_86 (coe v2))
    )

-- Haskell.Prim.Monoid.MonoidEndo
d_MonoidEndo_172 :: () -> T_Monoid_74
d_MonoidEndo_172 ~v0 = du_MonoidEndo_172
du_MonoidEndo_172 :: T_Monoid_74
du_MonoidEndo_172 =
  coe
    du_mkMonoid_142
    ( coe
        C_DefaultMonoid'46'constructor_4503
        (coe (\v0 -> v0))
        ( coe
            C_Semigroup'46'constructor_7
            (coe MAlonzo.Code.Haskell.Prim.du__'8728'__28)
        )
    )

-- Haskell.Prim.Monoid.MonoidEndoᵒᵖ
d_MonoidEndo'7506''7510'_176 :: () -> T_Monoid_74
d_MonoidEndo'7506''7510'_176 ~v0 = du_MonoidEndo'7506''7510'_176
du_MonoidEndo'7506''7510'_176 :: T_Monoid_74
du_MonoidEndo'7506''7510'_176 =
  coe
    du_mkMonoid_142
    ( coe
        C_DefaultMonoid'46'constructor_4503
        (coe (\v0 -> v0))
        ( coe
            C_Semigroup'46'constructor_7
            ( coe
                MAlonzo.Code.Haskell.Prim.du_flip_36
                (coe MAlonzo.Code.Haskell.Prim.du__'8728'__28)
            )
        )
    )

-- Haskell.Prim.Monoid.MonoidConj
d_MonoidConj_180 :: T_Monoid_74
d_MonoidConj_180 =
  coe
    du_mkMonoid_142
    ( coe
        C_DefaultMonoid'46'constructor_4503
        (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
        ( coe
            C_Semigroup'46'constructor_7
            (coe MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6)
        )
    )

-- Haskell.Prim.Monoid.MonoidDisj
d_MonoidDisj_184 :: T_Monoid_74
d_MonoidDisj_184 =
  coe
    du_mkMonoid_142
    ( coe
        C_DefaultMonoid'46'constructor_4503
        (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
        ( coe
            C_Semigroup'46'constructor_7
            (coe MAlonzo.Code.Haskell.Prim.Bool.d__'124''124'__10)
        )
    )
