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

module MAlonzo.Code.Haskell.Prim.Monad where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Haskell.Prim
import qualified MAlonzo.Code.Haskell.Prim.Applicative
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

-- Haskell.Prim.Monad.Do.Monad
d_Monad_10 a0 = ()
data T_Monad_10
  = C_Monad'46'constructor_383
      ( () ->
        () ->
        AgdaAny ->
        (AgdaAny -> AgdaAny) ->
        AgdaAny
      )
      MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8
      (() -> AgdaAny -> AgdaAny)
      (() -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny)
      (() -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny)

-- Haskell.Prim.Monad.Do.Monad._>>=_
d__'62''62''61'__24 ::
  T_Monad_10 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
d__'62''62''61'__24 v0 =
  case coe v0 of
    C_Monad'46'constructor_383 v1 v2 v3 v4 v5 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Monad.Do.Monad.super
d_super_26 ::
  T_Monad_10 -> MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8
d_super_26 v0 =
  case coe v0 of
    C_Monad'46'constructor_383 v1 v2 v3 v4 v5 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Monad.Do.Monad.return
d_return_28 :: T_Monad_10 -> () -> AgdaAny -> AgdaAny
d_return_28 v0 =
  case coe v0 of
    C_Monad'46'constructor_383 v1 v2 v3 v4 v5 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Monad.Do.Monad._>>_
d__'62''62'__30 ::
  T_Monad_10 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
d__'62''62'__30 v0 =
  case coe v0 of
    C_Monad'46'constructor_383 v1 v2 v3 v4 v5 -> coe v4
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Monad.Do.Monad._=<<_
d__'61''60''60'__32 ::
  T_Monad_10 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d__'61''60''60'__32 v0 =
  case coe v0 of
    C_Monad'46'constructor_383 v1 v2 v3 v4 v5 -> coe v5
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Monad.Do.DefaultMonad
d_DefaultMonad_36 a0 = ()
data T_DefaultMonad_36
  = C_DefaultMonad'46'constructor_751
      ( () ->
        () ->
        AgdaAny ->
        (AgdaAny -> AgdaAny) ->
        AgdaAny
      )
      MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8

-- Haskell.Prim.Monad.Do.DefaultMonad._>>=_
d__'62''62''61'__44 ::
  T_DefaultMonad_36 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
d__'62''62''61'__44 v0 =
  case coe v0 of
    C_DefaultMonad'46'constructor_751 v1 v2 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Monad.Do.DefaultMonad.super
d_super_46 ::
  T_DefaultMonad_36 ->
  MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8
d_super_46 v0 =
  case coe v0 of
    C_DefaultMonad'46'constructor_751 v1 v2 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Monad.Do.DefaultMonad.return
d_return_48 ::
  (() -> ()) -> T_DefaultMonad_36 -> () -> AgdaAny -> AgdaAny
d_return_48 ~v0 v1 ~v2 = du_return_48 v1
du_return_48 :: T_DefaultMonad_36 -> AgdaAny -> AgdaAny
du_return_48 v0 =
  coe
    MAlonzo.Code.Haskell.Prim.Applicative.d_pure_22
    (d_super_46 (coe v0))
    erased

-- Haskell.Prim.Monad.Do.DefaultMonad._>>_
d__'62''62'__50 ::
  (() -> ()) ->
  T_DefaultMonad_36 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
d__'62''62'__50 ~v0 v1 ~v2 ~v3 v4 v5 = du__'62''62'__50 v1 v4 v5
du__'62''62'__50 ::
  T_DefaultMonad_36 -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'62''62'__50 v0 v1 v2 =
  coe
    d__'62''62''61'__44
    v0
    erased
    erased
    v1
    (\v3 -> coe v2 erased)

-- Haskell.Prim.Monad.Do.DefaultMonad._=<<_
d__'61''60''60'__58 ::
  (() -> ()) ->
  T_DefaultMonad_36 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d__'61''60''60'__58 ~v0 v1 ~v2 ~v3 = du__'61''60''60'__58 v1
du__'61''60''60'__58 ::
  T_DefaultMonad_36 -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'61''60''60'__58 v0 =
  coe
    MAlonzo.Code.Haskell.Prim.du_flip_36
    (coe d__'62''62''61'__44 v0 erased erased)

-- Haskell.Prim.Monad.Do._._=<<_
d__'61''60''60'__62 ::
  T_Monad_10 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d__'61''60''60'__62 v0 = coe d__'61''60''60'__32 (coe v0)

-- Haskell.Prim.Monad.Do._._>>_
d__'62''62'__64 ::
  T_Monad_10 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
d__'62''62'__64 v0 = coe d__'62''62'__30 (coe v0)

-- Haskell.Prim.Monad.Do._._>>=_
d__'62''62''61'__66 ::
  T_Monad_10 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
d__'62''62''61'__66 v0 = coe d__'62''62''61'__24 (coe v0)

-- Haskell.Prim.Monad.Do._.return
d_return_68 :: T_Monad_10 -> () -> AgdaAny -> AgdaAny
d_return_68 v0 = coe d_return_28 (coe v0)

-- Haskell.Prim.Monad.Do._.super
d_super_70 ::
  T_Monad_10 -> MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8
d_super_70 v0 = coe d_super_26 (coe v0)

-- Haskell.Prim.Monad.Dont._>>=_
d__'62''62''61'__74 ::
  (() -> ()) ->
  () ->
  () ->
  T_Monad_10 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
d__'62''62''61'__74 ~v0 ~v1 ~v2 v3 = du__'62''62''61'__74 v3
du__'62''62''61'__74 ::
  T_Monad_10 -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'62''62''61'__74 v0 = coe d__'62''62''61'__24 v0 erased erased

-- Haskell.Prim.Monad.Dont._>>_
d__'62''62'__76 ::
  (() -> ()) ->
  () ->
  () ->
  T_Monad_10 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
d__'62''62'__76 ~v0 ~v1 ~v2 v3 = du__'62''62'__76 v3
du__'62''62'__76 ::
  T_Monad_10 -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'62''62'__76 v0 = coe d__'62''62'__30 v0 erased erased

-- Haskell.Prim.Monad.mapM₋
d_mapM'8331'_78 ::
  (() -> ()) ->
  (() -> ()) ->
  () ->
  () ->
  T_Monad_10 ->
  MAlonzo.Code.Haskell.Prim.Foldable.T_Foldable_8 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d_mapM'8331'_78 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 =
  du_mapM'8331'_78 v4 v5 v6
du_mapM'8331'_78 ::
  T_Monad_10 ->
  MAlonzo.Code.Haskell.Prim.Foldable.T_Foldable_8 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
du_mapM'8331'_78 v0 v1 v2 =
  coe
    MAlonzo.Code.Haskell.Prim.Foldable.d_foldr_50
    v1
    erased
    erased
    ( \v3 v4 ->
        coe d__'62''62'__30 v0 erased erased (coe v2 v3) (\v5 -> v4)
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.Applicative.d_pure_22
        (d_super_26 (coe v0))
        erased
        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
    )

-- Haskell.Prim.Monad.sequence₋
d_sequence'8331'_86 ::
  (() -> ()) ->
  (() -> ()) ->
  () ->
  T_Monad_10 ->
  MAlonzo.Code.Haskell.Prim.Foldable.T_Foldable_8 ->
  AgdaAny ->
  AgdaAny
d_sequence'8331'_86 ~v0 ~v1 ~v2 v3 v4 = du_sequence'8331'_86 v3 v4
du_sequence'8331'_86 ::
  T_Monad_10 ->
  MAlonzo.Code.Haskell.Prim.Foldable.T_Foldable_8 ->
  AgdaAny ->
  AgdaAny
du_sequence'8331'_86 v0 v1 =
  coe
    MAlonzo.Code.Haskell.Prim.Foldable.d_foldr_50
    v1
    erased
    erased
    (\v2 v3 -> coe d__'62''62'__30 v0 erased erased v2 (\v4 -> v3))
    ( coe
        MAlonzo.Code.Haskell.Prim.Applicative.d_pure_22
        (d_super_26 (coe v0))
        erased
        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
    )

-- Haskell.Prim.Monad._._=<<_
d__'61''60''60'__100 ::
  (() -> ()) ->
  T_DefaultMonad_36 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d__'61''60''60'__100 ~v0 v1 = du__'61''60''60'__100 v1
du__'61''60''60'__100 ::
  T_DefaultMonad_36 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
du__'61''60''60'__100 v0 v1 v2 = coe du__'61''60''60'__58 (coe v0)

-- Haskell.Prim.Monad._._>>_
d__'62''62'__102 ::
  (() -> ()) ->
  T_DefaultMonad_36 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
d__'62''62'__102 ~v0 v1 = du__'62''62'__102 v1
du__'62''62'__102 ::
  T_DefaultMonad_36 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
du__'62''62'__102 v0 v1 v2 v3 v4 =
  coe du__'62''62'__50 (coe v0) v3 v4

-- Haskell.Prim.Monad._._>>=_
d__'62''62''61'__104 ::
  T_DefaultMonad_36 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
d__'62''62''61'__104 v0 = coe d__'62''62''61'__44 (coe v0)

-- Haskell.Prim.Monad._.return
d_return_106 ::
  (() -> ()) -> T_DefaultMonad_36 -> () -> AgdaAny -> AgdaAny
d_return_106 ~v0 v1 = du_return_106 v1
du_return_106 :: T_DefaultMonad_36 -> () -> AgdaAny -> AgdaAny
du_return_106 v0 v1 = coe du_return_48 (coe v0)

-- Haskell.Prim.Monad._.super
d_super_108 ::
  T_DefaultMonad_36 ->
  MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8
d_super_108 v0 = coe d_super_46 (coe v0)

-- Haskell.Prim.Monad.bind=_
d_bind'61'__114 ::
  (() -> ()) ->
  MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
  (() -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny) ->
  T_Monad_10
d_bind'61'__114 ~v0 v1 v2 = du_bind'61'__114 v1 v2
du_bind'61'__114 ::
  MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
  (() -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny) ->
  T_Monad_10
du_bind'61'__114 v0 v1 =
  coe
    C_Monad'46'constructor_383
    (coe v1)
    (coe v0)
    ( \v2 ->
        coe
          du_return_48
          (coe C_DefaultMonad'46'constructor_751 (coe v1) (coe v0))
    )
    ( \v2 v3 v4 v5 ->
        coe
          du__'62''62'__50
          (coe C_DefaultMonad'46'constructor_751 (coe v1) (coe v0))
          v4
          v5
    )
    ( \v2 v3 ->
        coe
          du__'61''60''60'__58
          (coe C_DefaultMonad'46'constructor_751 (coe v1) (coe v0))
    )

-- Haskell.Prim.Monad._._=<<_
d__'61''60''60'__122 ::
  (() -> ()) ->
  MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
  (() -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny) ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d__'61''60''60'__122 ~v0 v1 v2 = du__'61''60''60'__122 v1 v2
du__'61''60''60'__122 ::
  MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
  (() -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny) ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
du__'61''60''60'__122 v0 v1 v2 v3 =
  coe
    du__'61''60''60'__58
    (coe C_DefaultMonad'46'constructor_751 (coe v1) (coe v0))

-- Haskell.Prim.Monad._._>>_
d__'62''62'__124 ::
  (() -> ()) ->
  MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
  (() -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny) ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
d__'62''62'__124 ~v0 v1 v2 = du__'62''62'__124 v1 v2
du__'62''62'__124 ::
  MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
  (() -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny) ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
du__'62''62'__124 v0 v1 v2 v3 v4 v5 =
  coe
    du__'62''62'__50
    (coe C_DefaultMonad'46'constructor_751 (coe v1) (coe v0))
    v4
    v5

-- Haskell.Prim.Monad._.return
d_return_128 ::
  (() -> ()) ->
  MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
  (() -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny) ->
  () ->
  AgdaAny ->
  AgdaAny
d_return_128 ~v0 v1 v2 = du_return_128 v1 v2
du_return_128 ::
  MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
  (() -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny) ->
  () ->
  AgdaAny ->
  AgdaAny
du_return_128 v0 v1 v2 =
  coe
    du_return_48
    (coe C_DefaultMonad'46'constructor_751 (coe v1) (coe v0))

-- Haskell.Prim.Monad.iMonadList
d_iMonadList_132 :: T_Monad_10
d_iMonadList_132 =
  coe
    du_bind'61'__114
    ( coe
        MAlonzo.Code.Haskell.Prim.Applicative.du_mkApplicative_76
        ( coe
            MAlonzo.Code.Haskell.Prim.Applicative.C_mk_62
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
    )
    ( coe
        ( \v0 v1 ->
            coe
              MAlonzo.Code.Haskell.Prim.du_flip_36
              ( coe
                  MAlonzo.Code.Haskell.Prim.Foldable.du_concatMap_190
                  ( coe
                      MAlonzo.Code.Haskell.Prim.Foldable.C_DefaultFoldable'46'constructor_4805
                      ( \v2 v3 v4 v5 v6 ->
                          coe
                            MAlonzo.Code.Haskell.Prim.Foldable.du_foldMapList_408
                            v4
                            v5
                            v6
                      )
                  )
              )
        )
    )

-- Haskell.Prim.Monad.iMonadMaybe
d_iMonadMaybe_134 :: T_Monad_10
d_iMonadMaybe_134 =
  coe
    du_bind'61'__114
    ( coe
        MAlonzo.Code.Haskell.Prim.Applicative.du_mkApplicative_76
        ( coe
            MAlonzo.Code.Haskell.Prim.Applicative.C_mk_62
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
    )
    ( coe
        ( \v0 v1 ->
            coe
              MAlonzo.Code.Haskell.Prim.du_flip_36
              ( coe
                  MAlonzo.Code.Haskell.Prim.Maybe.du_maybe_28
                  (coe MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16)
              )
        )
    )

-- Haskell.Prim.Monad.iMonadEither
d_iMonadEither_136 :: () -> T_Monad_10
d_iMonadEither_136 ~v0 = du_iMonadEither_136
du_iMonadEither_136 :: T_Monad_10
du_iMonadEither_136 =
  coe
    du_bind'61'__114
    ( coe
        MAlonzo.Code.Haskell.Prim.Applicative.du_mkApplicative_76
        ( coe
            MAlonzo.Code.Haskell.Prim.Applicative.C_mk_62
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
    )
    ( coe
        ( \v0 v1 ->
            coe
              MAlonzo.Code.Haskell.Prim.du_flip_36
              ( coe
                  MAlonzo.Code.Haskell.Prim.Either.du_either_20
                  (coe MAlonzo.Code.Haskell.Prim.Either.C_Left_16)
              )
        )
    )

-- Haskell.Prim.Monad.iMonadFun
d_iMonadFun_140 :: () -> T_Monad_10
d_iMonadFun_140 ~v0 = du_iMonadFun_140
du_iMonadFun_140 :: T_Monad_10
du_iMonadFun_140 =
  coe
    du_bind'61'__114
    ( coe
        MAlonzo.Code.Haskell.Prim.Applicative.du_mkApplicative_76
        ( coe
            MAlonzo.Code.Haskell.Prim.Applicative.C_mk_62
            (coe (\v0 v1 v2 -> v1))
            (coe (\v0 v1 v2 v3 v4 -> coe v2 v4 (coe v3 v4)))
            (coe MAlonzo.Code.Haskell.Prim.Functor.du_iFunctorFun_156)
        )
    )
    (coe (\v0 v1 v2 v3 v4 -> coe v3 (coe v2 v4) v4))

-- Haskell.Prim.Monad.iMonadTuple₂
d_iMonadTuple'8322'_150 ::
  () -> MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 -> T_Monad_10
d_iMonadTuple'8322'_150 ~v0 v1 = du_iMonadTuple'8322'_150 v1
du_iMonadTuple'8322'_150 ::
  MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 -> T_Monad_10
du_iMonadTuple'8322'_150 v0 =
  coe
    du_bind'61'__114
    ( coe
        MAlonzo.Code.Haskell.Prim.Applicative.du_mkApplicative_76
        ( coe
            MAlonzo.Code.Haskell.Prim.Applicative.C_mk_62
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
            ( coe
                MAlonzo.Code.Haskell.Prim.Functor.du_iFunctorTuple'8322'_160
            )
        )
    )
    ( coe
        ( \v1 v2 v3 v4 ->
            coe
              MAlonzo.Code.Haskell.Prim.Tuple.du_first_58
              ( coe
                  MAlonzo.Code.Haskell.Prim.Monoid.d__'60''62'__14
                  (MAlonzo.Code.Haskell.Prim.Monoid.d_super_88 (coe v0))
                  (MAlonzo.Code.Haskell.Prim.Tuple.d_fst_20 (coe v3))
              )
              (coe v4 (MAlonzo.Code.Haskell.Prim.Tuple.d_snd_22 (coe v3)))
        )
    )

-- Haskell.Prim.Monad.iMonadTuple₃
d_iMonadTuple'8323'_164 ::
  () ->
  () ->
  MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
  MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
  T_Monad_10
d_iMonadTuple'8323'_164 ~v0 ~v1 v2 v3 =
  du_iMonadTuple'8323'_164 v2 v3
du_iMonadTuple'8323'_164 ::
  MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
  MAlonzo.Code.Haskell.Prim.Monoid.T_Monoid_74 ->
  T_Monad_10
du_iMonadTuple'8323'_164 v0 v1 =
  coe
    du_bind'61'__114
    ( coe
        MAlonzo.Code.Haskell.Prim.Applicative.du_mkApplicative_76
        ( coe
            MAlonzo.Code.Haskell.Prim.Applicative.C_mk_62
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
            ( coe
                MAlonzo.Code.Haskell.Prim.Functor.du_iFunctorTuple'8323'_172
            )
        )
    )
    ( coe
        ( \v2 v3 v4 v5 ->
            case coe v4 of
              MAlonzo.Code.Haskell.Prim.Tuple.C__'44'_'44'__40 v6 v7 v8 ->
                coe
                  MAlonzo.Code.Haskell.Prim.du_case_of__58
                  (coe v5 v8)
                  ( coe
                      ( \v9 v10 ->
                          case coe v9 of
                            MAlonzo.Code.Haskell.Prim.Tuple.C__'44'_'44'__40 v11 v12 v13 ->
                              coe
                                MAlonzo.Code.Haskell.Prim.Tuple.C__'44'_'44'__40
                                ( coe
                                    MAlonzo.Code.Haskell.Prim.Monoid.d__'60''62'__14
                                    (MAlonzo.Code.Haskell.Prim.Monoid.d_super_88 (coe v0))
                                    v6
                                    v11
                                )
                                ( coe
                                    MAlonzo.Code.Haskell.Prim.Monoid.d__'60''62'__14
                                    (MAlonzo.Code.Haskell.Prim.Monoid.d_super_88 (coe v1))
                                    v7
                                    v12
                                )
                                (coe v13)
                            _ -> MAlonzo.RTE.mazUnreachableError
                      )
                  )
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )

-- Haskell.Prim.Monad.iMonadIO
d_iMonadIO_184 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Prim.Monad.iMonadIO"

-- Haskell.Prim.Monad.MonadFail
d_MonadFail_188 a0 = ()
data T_MonadFail_188
  = C_MonadFail'46'constructor_10091
      ( () ->
        [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
        AgdaAny
      )
      T_Monad_10

-- Haskell.Prim.Monad.MonadFail.fail
d_fail_196 ::
  T_MonadFail_188 ->
  () ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  AgdaAny
d_fail_196 v0 =
  case coe v0 of
    C_MonadFail'46'constructor_10091 v1 v2 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Monad.MonadFail.super
d_super_198 :: T_MonadFail_188 -> T_Monad_10
d_super_198 v0 =
  case coe v0 of
    C_MonadFail'46'constructor_10091 v1 v2 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Monad._.fail
d_fail_202 ::
  T_MonadFail_188 ->
  () ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  AgdaAny
d_fail_202 v0 = coe d_fail_196 (coe v0)

-- Haskell.Prim.Monad._.super
d_super_204 :: T_MonadFail_188 -> T_Monad_10
d_super_204 v0 = coe d_super_198 (coe v0)

-- Haskell.Prim.Monad.MonadFailList
d_MonadFailList_206 :: T_MonadFail_188
d_MonadFailList_206 =
  coe
    C_MonadFail'46'constructor_10091
    (coe (\v0 v1 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
    (coe d_iMonadList_132)

-- Haskell.Prim.Monad.MonadFailMaybe
d_MonadFailMaybe_208 :: T_MonadFail_188
d_MonadFailMaybe_208 =
  coe
    C_MonadFail'46'constructor_10091
    (coe (\v0 v1 -> coe MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16))
    (coe d_iMonadMaybe_134)
