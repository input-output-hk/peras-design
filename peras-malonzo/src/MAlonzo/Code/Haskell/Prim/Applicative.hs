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

module MAlonzo.Code.Haskell.Prim.Applicative where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Haskell.Prim.Either
import qualified MAlonzo.Code.Haskell.Prim.Foldable
import qualified MAlonzo.Code.Haskell.Prim.Functor
import qualified MAlonzo.Code.Haskell.Prim.List
import qualified MAlonzo.Code.Haskell.Prim.Maybe
import qualified MAlonzo.Code.Haskell.Prim.Monoid
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

-- Haskell.Prim.Applicative.Applicative
d_Applicative_8 a0 = ()
data T_Applicative_8
  = C_Applicative'46'constructor_363
      (() -> AgdaAny -> AgdaAny)
      (() -> () -> AgdaAny -> AgdaAny -> AgdaAny)
      MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8
      (() -> () -> AgdaAny -> AgdaAny -> AgdaAny)
      (() -> () -> AgdaAny -> AgdaAny -> AgdaAny)

-- Haskell.Prim.Applicative.Applicative.pure
d_pure_22 :: T_Applicative_8 -> () -> AgdaAny -> AgdaAny
d_pure_22 v0 =
  case coe v0 of
    C_Applicative'46'constructor_363 v1 v2 v3 v4 v5 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Applicative.Applicative._<*>_
d__'60''42''62'__24 ::
  T_Applicative_8 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__24 v0 =
  case coe v0 of
    C_Applicative'46'constructor_363 v1 v2 v3 v4 v5 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Applicative.Applicative.super
d_super_26 ::
  T_Applicative_8 -> MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8
d_super_26 v0 =
  case coe v0 of
    C_Applicative'46'constructor_363 v1 v2 v3 v4 v5 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Applicative.Applicative._<*_
d__'60''42'__28 ::
  T_Applicative_8 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42'__28 v0 =
  case coe v0 of
    C_Applicative'46'constructor_363 v1 v2 v3 v4 v5 -> coe v4
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Applicative.Applicative._*>_
d__'42''62'__30 ::
  T_Applicative_8 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'42''62'__30 v0 =
  case coe v0 of
    C_Applicative'46'constructor_363 v1 v2 v3 v4 v5 -> coe v5
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Applicative.DefaultApplicative
d_DefaultApplicative_34 a0 = ()
data T_DefaultApplicative_34
  = C_mk_62
      (() -> AgdaAny -> AgdaAny)
      (() -> () -> AgdaAny -> AgdaAny -> AgdaAny)
      MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8

-- Haskell.Prim.Applicative.DefaultApplicative.pure
d_pure_44 :: T_DefaultApplicative_34 -> () -> AgdaAny -> AgdaAny
d_pure_44 v0 =
  case coe v0 of
    C_mk_62 v1 v2 v3 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Applicative.DefaultApplicative._<*>_
d__'60''42''62'__46 ::
  T_DefaultApplicative_34 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d__'60''42''62'__46 v0 =
  case coe v0 of
    C_mk_62 v1 v2 v3 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Applicative.DefaultApplicative.super
d_super_48 ::
  T_DefaultApplicative_34 ->
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8
d_super_48 v0 =
  case coe v0 of
    C_mk_62 v1 v2 v3 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Applicative.DefaultApplicative._<*_
d__'60''42'__50 ::
  (() -> ()) ->
  T_DefaultApplicative_34 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d__'60''42'__50 ~v0 v1 ~v2 ~v3 v4 v5 = du__'60''42'__50 v1 v4 v5
du__'60''42'__50 ::
  T_DefaultApplicative_34 -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42'__50 v0 v1 v2 =
  coe
    d__'60''42''62'__46
    v0
    erased
    erased
    ( coe
        MAlonzo.Code.Haskell.Prim.Functor.d__'60''36''62'__26
        (d_super_48 (coe v0))
        erased
        erased
        (\v3 v4 -> v3)
        v1
    )
    v2

-- Haskell.Prim.Applicative.DefaultApplicative._*>_
d__'42''62'__56 ::
  (() -> ()) ->
  T_DefaultApplicative_34 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d__'42''62'__56 ~v0 v1 ~v2 ~v3 v4 v5 = du__'42''62'__56 v1 v4 v5
du__'42''62'__56 ::
  T_DefaultApplicative_34 -> AgdaAny -> AgdaAny -> AgdaAny
du__'42''62'__56 v0 v1 v2 =
  coe
    d__'60''42''62'__46
    v0
    erased
    erased
    ( coe
        MAlonzo.Code.Haskell.Prim.Functor.d__'60''36''62'__26
        (d_super_48 (coe v0))
        erased
        erased
        (let v3 = \v3 -> v3 in coe (\v4 -> v3))
        v1
    )
    v2

-- Haskell.Prim.Applicative._._*>_
d__'42''62'__66 ::
  T_Applicative_8 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'42''62'__66 v0 = coe d__'42''62'__30 (coe v0)

-- Haskell.Prim.Applicative._._<*_
d__'60''42'__68 ::
  T_Applicative_8 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42'__68 v0 = coe d__'60''42'__28 (coe v0)

-- Haskell.Prim.Applicative._._<*>_
d__'60''42''62'__70 ::
  T_Applicative_8 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__70 v0 = coe d__'60''42''62'__24 (coe v0)

-- Haskell.Prim.Applicative._.pure
d_pure_72 :: T_Applicative_8 -> () -> AgdaAny -> AgdaAny
d_pure_72 v0 = coe d_pure_22 (coe v0)

-- Haskell.Prim.Applicative._.super
d_super_74 ::
  T_Applicative_8 -> MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8
d_super_74 v0 = coe d_super_26 (coe v0)

-- Haskell.Prim.Applicative.mkApplicative
d_mkApplicative_76 ::
  (() -> ()) -> T_DefaultApplicative_34 -> T_Applicative_8
d_mkApplicative_76 ~v0 v1 = du_mkApplicative_76 v1
du_mkApplicative_76 :: T_DefaultApplicative_34 -> T_Applicative_8
du_mkApplicative_76 v0 =
  coe
    C_Applicative'46'constructor_363
    (coe d_pure_44 (coe v0))
    (coe d__'60''42''62'__46 (coe v0))
    (coe d_super_48 (coe v0))
    (\v1 v2 v3 v4 -> coe du__'60''42'__50 (coe v0) v3 v4)
    (\v1 v2 v3 v4 -> coe du__'42''62'__56 (coe v0) v3 v4)

-- Haskell.Prim.Applicative._._*>_
d__'42''62'__84 ::
  (() -> ()) ->
  T_DefaultApplicative_34 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d__'42''62'__84 ~v0 v1 = du__'42''62'__84 v1
du__'42''62'__84 ::
  T_DefaultApplicative_34 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
du__'42''62'__84 v0 v1 v2 v3 v4 =
  coe du__'42''62'__56 (coe v0) v3 v4

-- Haskell.Prim.Applicative._._<*_
d__'60''42'__86 ::
  (() -> ()) ->
  T_DefaultApplicative_34 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d__'60''42'__86 ~v0 v1 = du__'60''42'__86 v1
du__'60''42'__86 ::
  T_DefaultApplicative_34 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
du__'60''42'__86 v0 v1 v2 v3 v4 =
  coe du__'60''42'__50 (coe v0) v3 v4

-- Haskell.Prim.Applicative._._<*>_
d__'60''42''62'__88 ::
  T_DefaultApplicative_34 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d__'60''42''62'__88 v0 = coe d__'60''42''62'__46 (coe v0)

-- Haskell.Prim.Applicative._.pure
d_pure_90 :: T_DefaultApplicative_34 -> () -> AgdaAny -> AgdaAny
d_pure_90 v0 = coe d_pure_44 (coe v0)

-- Haskell.Prim.Applicative._.super
d_super_92 ::
  T_DefaultApplicative_34 ->
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8
d_super_92 v0 = coe d_super_48 (coe v0)

-- Haskell.Prim.Applicative.iApplicativeList
d_iApplicativeList_94 :: T_Applicative_8
d_iApplicativeList_94 =
  coe
    du_mkApplicative_76
    ( coe
        C_mk_62
        ( coe
            ( \v0 v1 ->
                coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe v1)
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
            )
        )
        ( coe
            ( \v0 v1 v2 v3 ->
                coe
                  MAlonzo.Code.Haskell.Prim.Foldable.du_concatMap_190
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
                  ( \v4 ->
                      coe MAlonzo.Code.Haskell.Prim.List.du_map_6 (coe v4) (coe v3)
                  )
                  v2
            )
        )
        (coe MAlonzo.Code.Haskell.Prim.Functor.d_iFunctorList_130)
    )

-- Haskell.Prim.Applicative.iApplicativeMaybe
d_iApplicativeMaybe_106 :: T_Applicative_8
d_iApplicativeMaybe_106 =
  coe
    du_mkApplicative_76
    ( coe
        C_mk_62
        (coe (\v0 -> coe MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18))
        ( coe
            ( \v0 v1 v2 ->
                let v3 =
                      \v3 -> coe MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16
                 in coe
                      ( case coe v2 of
                          MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 v4 ->
                            coe
                              ( \v5 ->
                                  let v6 = coe MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16
                                   in coe
                                        ( case coe v5 of
                                            MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 v7 ->
                                              coe MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 (coe v4 v7)
                                            _ -> coe v6
                                        )
                              )
                          _ -> coe v3
                      )
            )
        )
        (coe MAlonzo.Code.Haskell.Prim.Functor.d_iFunctorMaybe_132)
    )

-- Haskell.Prim.Applicative.iApplicativeEither
d_iApplicativeEither_114 :: () -> T_Applicative_8
d_iApplicativeEither_114 ~v0 = du_iApplicativeEither_114
du_iApplicativeEither_114 :: T_Applicative_8
du_iApplicativeEither_114 =
  coe
    du_mkApplicative_76
    ( coe
        C_mk_62
        (coe (\v0 -> coe MAlonzo.Code.Haskell.Prim.Either.C_Right_18))
        ( coe
            ( \v0 v1 v2 ->
                case coe v2 of
                  MAlonzo.Code.Haskell.Prim.Either.C_Left_16 v3 -> coe (\v4 -> v2)
                  MAlonzo.Code.Haskell.Prim.Either.C_Right_18 v3 ->
                    coe
                      ( \v4 ->
                          case coe v4 of
                            MAlonzo.Code.Haskell.Prim.Either.C_Right_18 v5 ->
                              coe MAlonzo.Code.Haskell.Prim.Either.C_Right_18 (coe v3 v5)
                            MAlonzo.Code.Haskell.Prim.Either.C_Left_16 v5 -> coe v4
                            _ -> MAlonzo.RTE.mazUnreachableError
                      )
                  _ -> MAlonzo.RTE.mazUnreachableError
            )
        )
        (coe MAlonzo.Code.Haskell.Prim.Functor.du_iFunctorEither_142)
    )

-- Haskell.Prim.Applicative.iApplicativeFun
d_iApplicativeFun_128 :: () -> T_Applicative_8
d_iApplicativeFun_128 ~v0 = du_iApplicativeFun_128
du_iApplicativeFun_128 :: T_Applicative_8
du_iApplicativeFun_128 =
  coe
    du_mkApplicative_76
    ( coe
        C_mk_62
        (coe (\v0 v1 v2 -> v1))
        (coe (\v0 v1 v2 v3 v4 -> coe v2 v4 (coe v3 v4)))
        (coe MAlonzo.Code.Haskell.Prim.Functor.du_iFunctorFun_156)
    )

-- Haskell.Prim.Applicative.iApplicativeTuple₂
d_iApplicativeTuple'8322'_140 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
  T_Applicative_8
d_iApplicativeTuple'8322'_140 ~v0 v1 =
  du_iApplicativeTuple'8322'_140 v1
du_iApplicativeTuple'8322'_140 ::
  MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 -> T_Applicative_8
du_iApplicativeTuple'8322'_140 v0 =
  coe
    du_mkApplicative_76
    ( coe
        C_mk_62
        ( coe
            ( \v1 v2 ->
                coe
                  MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24
                  (coe MAlonzo.Code.Haskell.Prim.Monoid.d_mempty_86 (coe v0))
                  (coe v2)
            )
        )
        ( coe
            ( \v1 v2 v3 ->
                case coe v3 of
                  MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24 v4 v5 ->
                    coe
                      ( \v6 ->
                          case coe v6 of
                            MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24 v7 v8 ->
                              coe
                                MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24
                                ( coe
                                    MAlonzo.Code.Haskell.Prim.Monoid.d__'60''62'__14
                                    (MAlonzo.Code.Haskell.Prim.Monoid.d_super_88 (coe v0))
                                    v4
                                    v7
                                )
                                (coe v5 v8)
                            _ -> MAlonzo.RTE.mazUnreachableError
                      )
                  _ -> MAlonzo.RTE.mazUnreachableError
            )
        )
        (coe MAlonzo.Code.Haskell.Prim.Functor.du_iFunctorTuple'8322'_160)
    )

-- Haskell.Prim.Applicative.iApplicativeTuple₃
d_iApplicativeTuple'8323'_156 ::
  () ->
  () ->
  MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
  MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
  T_Applicative_8
d_iApplicativeTuple'8323'_156 ~v0 ~v1 v2 v3 =
  du_iApplicativeTuple'8323'_156 v2 v3
du_iApplicativeTuple'8323'_156 ::
  MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
  MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
  T_Applicative_8
du_iApplicativeTuple'8323'_156 v0 v1 =
  coe
    du_mkApplicative_76
    ( coe
        C_mk_62
        ( coe
            ( \v2 v3 ->
                coe
                  MAlonzo.Code.Haskell.Prim.Tuple.C__'44'_'44'__40
                  (coe MAlonzo.Code.Haskell.Prim.Monoid.d_mempty_86 (coe v0))
                  (coe MAlonzo.Code.Haskell.Prim.Monoid.d_mempty_86 (coe v1))
                  (coe v3)
            )
        )
        ( coe
            ( \v2 v3 v4 ->
                case coe v4 of
                  MAlonzo.Code.Haskell.Prim.Tuple.C__'44'_'44'__40 v5 v6 v7 ->
                    coe
                      ( \v8 ->
                          case coe v8 of
                            MAlonzo.Code.Haskell.Prim.Tuple.C__'44'_'44'__40 v9 v10 v11 ->
                              coe
                                MAlonzo.Code.Haskell.Prim.Tuple.C__'44'_'44'__40
                                ( coe
                                    MAlonzo.Code.Haskell.Prim.Monoid.d__'60''62'__14
                                    (MAlonzo.Code.Haskell.Prim.Monoid.d_super_88 (coe v0))
                                    v5
                                    v9
                                )
                                ( coe
                                    MAlonzo.Code.Haskell.Prim.Monoid.d__'60''62'__14
                                    (MAlonzo.Code.Haskell.Prim.Monoid.d_super_88 (coe v1))
                                    v6
                                    v10
                                )
                                (coe v7 v11)
                            _ -> MAlonzo.RTE.mazUnreachableError
                      )
                  _ -> MAlonzo.RTE.mazUnreachableError
            )
        )
        (coe MAlonzo.Code.Haskell.Prim.Functor.du_iFunctorTuple'8323'_172)
    )

-- Haskell.Prim.Applicative.iApplicativeIO
d_iApplicativeIO_174 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Prim.Applicative.iApplicativeIO"
