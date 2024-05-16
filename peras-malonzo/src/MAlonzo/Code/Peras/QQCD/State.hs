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

module MAlonzo.Code.Peras.QQCD.State where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Haskell.Prim
import qualified MAlonzo.Code.Haskell.Prim.Applicative
import qualified MAlonzo.Code.Haskell.Prim.Functor
import qualified MAlonzo.Code.Haskell.Prim.Monad
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

-- Peras.QCD.State.State
d_State_10 a0 a1 = ()
newtype T_State_10
  = C_State'46'constructor_13
      ( AgdaAny ->
        MAlonzo.Code.Haskell.Prim.Tuple.T__'215'__10
      )

-- Peras.QCD.State.State.runState
d_runState_18 ::
  T_State_10 ->
  AgdaAny ->
  MAlonzo.Code.Haskell.Prim.Tuple.T__'215'__10
d_runState_18 v0 =
  case coe v0 of
    C_State'46'constructor_13 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.State.makeState
d_makeState_24 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Haskell.Prim.Tuple.T__'215'__10) ->
  T_State_10
d_makeState_24 ~v0 ~v1 v2 = du_makeState_24 v2
du_makeState_24 ::
  (AgdaAny -> MAlonzo.Code.Haskell.Prim.Tuple.T__'215'__10) ->
  T_State_10
du_makeState_24 v0 = coe C_State'46'constructor_13 (coe v0)

-- Peras.QCD.State.execState
d_execState_32 :: T_State_10 -> AgdaAny -> AgdaAny
d_execState_32 v0 v1 =
  coe
    MAlonzo.Code.Haskell.Prim.Tuple.d_snd_22
    (coe d_runState_18 v0 v1)

-- Peras.QCD.State.evalState
d_evalState_42 :: T_State_10 -> AgdaAny -> AgdaAny
d_evalState_42 v0 v1 =
  coe
    MAlonzo.Code.Haskell.Prim.Tuple.d_fst_20
    (coe d_runState_18 v0 v1)

-- Peras.QCD.State.getState
d_getState_50 :: () -> T_State_10
d_getState_50 ~v0 = du_getState_50
du_getState_50 :: T_State_10
du_getState_50 =
  coe
    C_State'46'constructor_13
    ( coe
        ( \v0 ->
            coe MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24 (coe v0) (coe v0)
        )
    )

-- Peras.QCD.State.putState
d_putState_56 :: () -> AgdaAny -> T_State_10
d_putState_56 ~v0 v1 = du_putState_56 v1
du_putState_56 :: AgdaAny -> T_State_10
du_putState_56 v0 =
  coe
    C_State'46'constructor_13
    ( coe
        ( \v1 ->
            coe
              MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24
              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
              (coe v0)
        )
    )

-- Peras.QCD.State.fmapState
d_fmapState_68 ::
  () -> () -> () -> (AgdaAny -> AgdaAny) -> T_State_10 -> T_State_10
d_fmapState_68 ~v0 ~v1 ~v2 v3 v4 = du_fmapState_68 v3 v4
du_fmapState_68 :: (AgdaAny -> AgdaAny) -> T_State_10 -> T_State_10
du_fmapState_68 v0 v1 =
  coe
    MAlonzo.Code.Haskell.Prim.du__'36'__48
    (coe du_makeState_24)
    ( coe
        ( \v2 ->
            coe
              MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24
              ( coe
                  v0
                  ( MAlonzo.Code.Haskell.Prim.Tuple.d_fst_20
                      (coe d_runState_18 v1 v2)
                  )
              )
              ( coe
                  MAlonzo.Code.Haskell.Prim.Tuple.d_snd_22
                  (coe d_runState_18 v1 v2)
              )
        )
    )

-- Peras.QCD.State.pureState
d_pureState_82 :: () -> () -> AgdaAny -> T_State_10
d_pureState_82 ~v0 ~v1 v2 = du_pureState_82 v2
du_pureState_82 :: AgdaAny -> T_State_10
du_pureState_82 v0 =
  coe
    C_State'46'constructor_13
    ( coe
        ( \v1 ->
            coe MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24 (coe v0) (coe v1)
        )
    )

-- Peras.QCD.State.apState
d_apState_94 ::
  () -> () -> () -> T_State_10 -> T_State_10 -> T_State_10
d_apState_94 ~v0 ~v1 ~v2 v3 v4 = du_apState_94 v3 v4
du_apState_94 :: T_State_10 -> T_State_10 -> T_State_10
du_apState_94 v0 v1 =
  coe
    MAlonzo.Code.Haskell.Prim.du__'36'__48
    (coe du_makeState_24)
    ( coe
        ( \v2 ->
            coe
              MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24
              ( coe
                  MAlonzo.Code.Haskell.Prim.Tuple.d_fst_20
                  (coe d_runState_18 v0 v2)
                  ( MAlonzo.Code.Haskell.Prim.Tuple.d_fst_20
                      ( coe
                          d_runState_18
                          v1
                          ( MAlonzo.Code.Haskell.Prim.Tuple.d_snd_22
                              (coe d_runState_18 v0 v2)
                          )
                      )
                  )
              )
              ( coe
                  MAlonzo.Code.Haskell.Prim.Tuple.d_snd_22
                  ( coe
                      d_runState_18
                      v1
                      ( MAlonzo.Code.Haskell.Prim.Tuple.d_snd_22
                          (coe d_runState_18 v0 v2)
                      )
                  )
              )
        )
    )

-- Peras.QCD.State.bindState
d_bindState_114 ::
  () ->
  () ->
  () ->
  T_State_10 ->
  (AgdaAny -> T_State_10) ->
  T_State_10
d_bindState_114 ~v0 ~v1 ~v2 v3 v4 = du_bindState_114 v3 v4
du_bindState_114 ::
  T_State_10 -> (AgdaAny -> T_State_10) -> T_State_10
du_bindState_114 v0 v1 =
  coe
    MAlonzo.Code.Haskell.Prim.du__'36'__48
    (coe du_makeState_24)
    ( coe
        ( \v2 ->
            coe
              d_runState_18
              ( coe
                  v1
                  ( MAlonzo.Code.Haskell.Prim.Tuple.d_fst_20
                      (coe d_runState_18 v0 v2)
                  )
              )
              ( MAlonzo.Code.Haskell.Prim.Tuple.d_snd_22
                  (coe d_runState_18 v0 v2)
              )
        )
    )

-- Peras.QCD.State.fmap=_
d_fmap'61'__130 ::
  (() -> ()) ->
  (() -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8
d_fmap'61'__130 ~v0 v1 = du_fmap'61'__130 v1
du_fmap'61'__130 ::
  (() -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8
du_fmap'61'__130 v0 =
  coe
    MAlonzo.Code.Haskell.Prim.Functor.C_Functor'46'constructor_585
    (coe v0)
    ( \v1 v2 ->
        coe
          MAlonzo.Code.Haskell.Prim.Functor.du__'60''36''62'__46
          ( coe
              MAlonzo.Code.Haskell.Prim.Functor.C_DefaultFunctor'46'constructor_1081
              (coe v0)
          )
    )
    ( \v1 v2 v3 v4 ->
        coe
          MAlonzo.Code.Haskell.Prim.Functor.du__'60''38''62'__48
          ( coe
              MAlonzo.Code.Haskell.Prim.Functor.C_DefaultFunctor'46'constructor_1081
              (coe v0)
          )
          v3
          v4
    )
    ( \v1 v2 v3 v4 ->
        coe
          MAlonzo.Code.Haskell.Prim.Functor.du__'60''36'__54
          ( coe
              MAlonzo.Code.Haskell.Prim.Functor.C_DefaultFunctor'46'constructor_1081
              (coe v0)
          )
          v3
          v4
    )
    ( \v1 v2 v3 v4 ->
        coe
          MAlonzo.Code.Haskell.Prim.Functor.du__'36''62'__62
          ( coe
              MAlonzo.Code.Haskell.Prim.Functor.C_DefaultFunctor'46'constructor_1081
              (coe v0)
          )
          v3
          v4
    )
    ( \v1 ->
        coe
          MAlonzo.Code.Haskell.Prim.Functor.du_void_68
          ( coe
              MAlonzo.Code.Haskell.Prim.Functor.C_DefaultFunctor'46'constructor_1081
              (coe v0)
          )
    )

-- Peras.QCD.State.iFunctorState
d_iFunctorState_152 ::
  () -> MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8
d_iFunctorState_152 ~v0 = du_iFunctorState_152
du_iFunctorState_152 ::
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8
du_iFunctorState_152 =
  coe du_fmap'61'__130 (\v0 v1 v2 v3 -> coe du_fmapState_68 v2 v3)

-- Peras.QCD.State.iApplicativeState
d_iApplicativeState_156 ::
  () -> MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8
d_iApplicativeState_156 ~v0 = du_iApplicativeState_156
du_iApplicativeState_156 ::
  MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8
du_iApplicativeState_156 =
  coe
    MAlonzo.Code.Haskell.Prim.Applicative.C_Applicative'46'constructor_363
    (coe (\v0 v1 -> coe du_pureState_82 (coe v1)))
    (coe (\v0 v1 v2 v3 -> coe du_apState_94 (coe v2) (coe v3)))
    (coe du_iFunctorState_152)
    ( coe
        ( \v0 v1 v2 v3 ->
            coe
              du_apState_94
              (coe du_fmapState_68 (coe (\v4 v5 -> v4)) (coe v2))
              (coe v3)
        )
    )
    ( coe
        ( \v0 v1 v2 v3 ->
            coe
              du_apState_94
              ( coe
                  du_fmapState_68
                  (let v4 = \v4 -> v4 in coe (coe (\v5 -> v4)))
                  (coe v2)
              )
              (coe v3)
        )
    )

-- Peras.QCD.State.iMonadState
d_iMonadState_174 ::
  () -> MAlonzo.Code.Haskell.Prim.Monad.T_Monad_10
d_iMonadState_174 ~v0 = du_iMonadState_174
du_iMonadState_174 :: MAlonzo.Code.Haskell.Prim.Monad.T_Monad_10
du_iMonadState_174 =
  coe
    MAlonzo.Code.Haskell.Prim.Monad.C_Monad'46'constructor_383
    (coe (\v0 v1 v2 v3 -> coe du_bindState_114 (coe v2) (coe v3)))
    (coe du_iApplicativeState_156)
    (coe (\v0 v1 -> coe du_pureState_82 (coe v1)))
    ( coe
        ( \v0 v1 v2 v3 ->
            coe du_bindState_114 (coe v2) (coe (\v4 -> coe v3 erased))
        )
    )
    (coe (\v0 v1 v2 v3 -> coe du_bindState_114 (coe v3) (coe v2)))

-- Peras.QCD.State.Lens'
d_Lens''_192 :: () -> () -> ()
d_Lens''_192 = erased

-- Peras.QCD.State.lens'
d_lens''_206 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (() -> ()) ->
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d_lens''_206 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 =
  du_lens''_206 v2 v3 v5 v6 v7
du_lens''_206 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
du_lens''_206 v0 v1 v2 v3 v4 =
  coe
    MAlonzo.Code.Haskell.Prim.Functor.d__'60''36''62'__26
    v2
    erased
    erased
    (coe v1 v4)
    (coe v3 (coe v0 v4))

-- Peras.QCD.State.Const
d_Const_220 a0 a1 = ()
newtype T_Const_220 = C_MakeConst_230 AgdaAny

-- Peras.QCD.State.Const.getConst
d_getConst_228 :: T_Const_220 -> AgdaAny
d_getConst_228 v0 =
  case coe v0 of
    C_MakeConst_230 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.State.fmapConst
d_fmapConst_238 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  T_Const_220 ->
  T_Const_220
d_fmapConst_238 ~v0 ~v1 ~v2 ~v3 v4 = du_fmapConst_238 v4
du_fmapConst_238 :: T_Const_220 -> T_Const_220
du_fmapConst_238 v0 =
  coe
    MAlonzo.Code.Haskell.Prim.du__'36'__48
    (coe C_MakeConst_230)
    (coe d_getConst_228 (coe v0))

-- Peras.QCD.State.iFunctorConst
d_iFunctorConst_244 ::
  () -> MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8
d_iFunctorConst_244 ~v0 = du_iFunctorConst_244
du_iFunctorConst_244 ::
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8
du_iFunctorConst_244 =
  coe du_fmap'61'__130 (\v0 v1 v2 v3 -> coe du_fmapConst_238 v3)

-- Peras.QCD.State.getField
d_getField_250 ::
  () ->
  () ->
  ( (() -> ()) ->
    MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  AgdaAny ->
  AgdaAny
d_getField_250 ~v0 ~v1 v2 v3 = du_getField_250 v2 v3
du_getField_250 ::
  ( (() -> ()) ->
    MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  AgdaAny ->
  AgdaAny
du_getField_250 v0 v1 =
  coe
    MAlonzo.Code.Haskell.Prim.du__'36'__48
    (coe (\v2 -> d_getConst_228 (coe v2)))
    ( coe
        v0
        erased
        (coe du_fmap'61'__130 (\v2 v3 v4 v5 -> coe du_fmapConst_238 v5))
        (coe C_MakeConst_230)
        v1
    )

-- Peras.QCD.State.use
d_use_260 ::
  () ->
  () ->
  ( (() -> ()) ->
    MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  T_State_10
d_use_260 ~v0 ~v1 v2 = du_use_260 v2
du_use_260 ::
  ( (() -> ()) ->
    MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  T_State_10
du_use_260 v0 =
  coe
    MAlonzo.Code.Haskell.Prim.Functor.du__'60''36''62'__46
    ( coe
        MAlonzo.Code.Haskell.Prim.Functor.C_DefaultFunctor'46'constructor_1081
        (\v1 v2 v3 v4 -> coe du_fmapState_68 v3 v4)
    )
    (coe du_getField_250 (coe v0))
    (coe du_getState_50)

-- Peras.QCD.State.Identity
d_Identity_266 a0 = ()
newtype T_Identity_266 = C_MakeIdentity_274 AgdaAny

-- Peras.QCD.State.Identity.runIdentity
d_runIdentity_272 :: T_Identity_266 -> AgdaAny
d_runIdentity_272 v0 =
  case coe v0 of
    C_MakeIdentity_274 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.State.fmapIdentity
d_fmapIdentity_280 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  T_Identity_266 ->
  T_Identity_266
d_fmapIdentity_280 ~v0 ~v1 v2 v3 = du_fmapIdentity_280 v2 v3
du_fmapIdentity_280 ::
  (AgdaAny -> AgdaAny) -> T_Identity_266 -> T_Identity_266
du_fmapIdentity_280 v0 v1 =
  coe
    MAlonzo.Code.Haskell.Prim.du__'36'__48
    ( coe
        MAlonzo.Code.Haskell.Prim.du__'8728'__28
        (coe C_MakeIdentity_274)
        (coe v0)
    )
    (coe d_runIdentity_272 (coe v1))

-- Peras.QCD.State.iFunctorIdentity
d_iFunctorIdentity_286 ::
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8
d_iFunctorIdentity_286 =
  coe
    du_fmap'61'__130
    (\v0 v1 v2 v3 -> coe du_fmapIdentity_280 v2 v3)

-- Peras.QCD.State.setField
d_setField_292 ::
  () ->
  () ->
  ( (() -> ()) ->
    MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d_setField_292 ~v0 ~v1 v2 v3 v4 = du_setField_292 v2 v3 v4
du_setField_292 ::
  ( (() -> ()) ->
    MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
du_setField_292 v0 v1 v2 =
  coe
    d_runIdentity_272
    ( coe
        v0
        erased
        ( coe
            du_fmap'61'__130
            (\v3 v4 v5 v6 -> coe du_fmapIdentity_280 v5 v6)
        )
        (\v3 -> coe C_MakeIdentity_274 (coe v1))
        v2
    )

-- Peras.QCD.State.assign
d_assign_306 ::
  () ->
  () ->
  ( (() -> ()) ->
    MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  AgdaAny ->
  T_State_10
d_assign_306 ~v0 ~v1 v2 v3 = du_assign_306 v2 v3
du_assign_306 ::
  ( (() -> ()) ->
    MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  AgdaAny ->
  T_State_10
du_assign_306 v0 v1 =
  coe
    du_bindState_114
    (coe du_getState_50)
    ( coe
        MAlonzo.Code.Haskell.Prim.du__'8728'__28
        (coe du_putState_56)
        (coe du_setField_292 (coe v0) (coe v1))
    )

-- Peras.QCD.State._≔_
d__'8788'__316 ::
  () ->
  () ->
  ( (() -> ()) ->
    MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  AgdaAny ->
  T_State_10
d__'8788'__316 ~v0 ~v1 = du__'8788'__316
du__'8788'__316 ::
  ( (() -> ()) ->
    MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  AgdaAny ->
  T_State_10
du__'8788'__316 = coe du_assign_306

-- Peras.QCD.State.modifying
d_modifying_322 ::
  () ->
  () ->
  ( (() -> ()) ->
    MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  (AgdaAny -> AgdaAny) ->
  T_State_10
d_modifying_322 ~v0 ~v1 v2 v3 = du_modifying_322 v2 v3
du_modifying_322 ::
  ( (() -> ()) ->
    MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  (AgdaAny -> AgdaAny) ->
  T_State_10
du_modifying_322 v0 v1 =
  coe
    du_bindState_114
    (coe du_use_260 (coe v0))
    ( coe
        MAlonzo.Code.Haskell.Prim.du__'8728'__28
        (coe du_assign_306 (coe v0))
        (coe v1)
    )

-- Peras.QCD.State._≕_
d__'8789'__332 ::
  () ->
  () ->
  ( (() -> ()) ->
    MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  (AgdaAny -> AgdaAny) ->
  T_State_10
d__'8789'__332 ~v0 ~v1 = du__'8789'__332
du__'8789'__332 ::
  ( (() -> ()) ->
    MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  (AgdaAny -> AgdaAny) ->
  T_State_10
du__'8789'__332 = coe du_modifying_322
