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

module MAlonzo.Code.Haskell.Prim.Functor where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Haskell.Prim
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

-- Haskell.Prim.Functor.Functor
d_Functor_8 a0 = ()
data T_Functor_8
  = C_Functor'46'constructor_585
      ( () ->
        () ->
        (AgdaAny -> AgdaAny) ->
        AgdaAny ->
        AgdaAny
      )
      (() -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny)
      (() -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny)
      (() -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny)
      (() -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny)
      (() -> AgdaAny -> AgdaAny)

-- Haskell.Prim.Functor.Functor.fmap
d_fmap_24 ::
  T_Functor_8 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d_fmap_24 v0 =
  case coe v0 of
    C_Functor'46'constructor_585 v1 v2 v3 v4 v5 v6 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Functor.Functor._<$>_
d__'60''36''62'__26 ::
  T_Functor_8 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d__'60''36''62'__26 v0 =
  case coe v0 of
    C_Functor'46'constructor_585 v1 v2 v3 v4 v5 v6 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Functor.Functor._<&>_
d__'60''38''62'__28 ::
  T_Functor_8 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
d__'60''38''62'__28 v0 =
  case coe v0 of
    C_Functor'46'constructor_585 v1 v2 v3 v4 v5 v6 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Functor.Functor._<$_
d__'60''36'__30 ::
  T_Functor_8 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d__'60''36'__30 v0 =
  case coe v0 of
    C_Functor'46'constructor_585 v1 v2 v3 v4 v5 v6 -> coe v4
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Functor.Functor._$>_
d__'36''62'__32 ::
  T_Functor_8 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
d__'36''62'__32 v0 =
  case coe v0 of
    C_Functor'46'constructor_585 v1 v2 v3 v4 v5 v6 -> coe v5
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Functor.Functor.void
d_void_34 :: T_Functor_8 -> () -> AgdaAny -> AgdaAny
d_void_34 v0 =
  case coe v0 of
    C_Functor'46'constructor_585 v1 v2 v3 v4 v5 v6 -> coe v6
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Functor.DefaultFunctor
d_DefaultFunctor_38 a0 = ()
newtype T_DefaultFunctor_38
  = C_DefaultFunctor'46'constructor_1081
      ( () ->
        () ->
        (AgdaAny -> AgdaAny) ->
        AgdaAny ->
        AgdaAny
      )

-- Haskell.Prim.Functor.DefaultFunctor.fmap
d_fmap_44 ::
  T_DefaultFunctor_38 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d_fmap_44 v0 =
  case coe v0 of
    C_DefaultFunctor'46'constructor_1081 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Functor.DefaultFunctor._<$>_
d__'60''36''62'__46 ::
  (() -> ()) ->
  T_DefaultFunctor_38 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d__'60''36''62'__46 ~v0 v1 ~v2 ~v3 = du__'60''36''62'__46 v1
du__'60''36''62'__46 ::
  T_DefaultFunctor_38 -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''36''62'__46 v0 = coe d_fmap_44 v0 erased erased

-- Haskell.Prim.Functor.DefaultFunctor._<&>_
d__'60''38''62'__48 ::
  (() -> ()) ->
  T_DefaultFunctor_38 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
d__'60''38''62'__48 ~v0 v1 ~v2 ~v3 v4 v5 =
  du__'60''38''62'__48 v1 v4 v5
du__'60''38''62'__48 ::
  T_DefaultFunctor_38 -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'60''38''62'__48 v0 v1 v2 =
  coe d_fmap_44 v0 erased erased v2 v1

-- Haskell.Prim.Functor.DefaultFunctor._<$_
d__'60''36'__54 ::
  (() -> ()) ->
  T_DefaultFunctor_38 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d__'60''36'__54 ~v0 v1 ~v2 ~v3 v4 v5 = du__'60''36'__54 v1 v4 v5
du__'60''36'__54 ::
  T_DefaultFunctor_38 -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''36'__54 v0 v1 v2 =
  coe d_fmap_44 v0 erased erased (\v3 -> coe v1 erased) v2

-- Haskell.Prim.Functor.DefaultFunctor._$>_
d__'36''62'__62 ::
  (() -> ()) ->
  T_DefaultFunctor_38 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
d__'36''62'__62 ~v0 v1 ~v2 ~v3 v4 v5 = du__'36''62'__62 v1 v4 v5
du__'36''62'__62 ::
  T_DefaultFunctor_38 -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'36''62'__62 v0 v1 v2 =
  coe du__'60''36'__54 (coe v0) (coe v2) (coe v1)

-- Haskell.Prim.Functor.DefaultFunctor.void
d_void_68 ::
  (() -> ()) -> T_DefaultFunctor_38 -> () -> AgdaAny -> AgdaAny
d_void_68 ~v0 v1 ~v2 = du_void_68 v1
du_void_68 :: T_DefaultFunctor_38 -> AgdaAny -> AgdaAny
du_void_68 v0 =
  coe
    du__'60''36'__54
    (coe v0)
    (coe (\v1 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))

-- Haskell.Prim.Functor._._$>_
d__'36''62'__74 ::
  T_Functor_8 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
d__'36''62'__74 v0 = coe d__'36''62'__32 (coe v0)

-- Haskell.Prim.Functor._._<$_
d__'60''36'__76 ::
  T_Functor_8 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d__'60''36'__76 v0 = coe d__'60''36'__30 (coe v0)

-- Haskell.Prim.Functor._._<$>_
d__'60''36''62'__78 ::
  T_Functor_8 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d__'60''36''62'__78 v0 = coe d__'60''36''62'__26 (coe v0)

-- Haskell.Prim.Functor._._<&>_
d__'60''38''62'__80 ::
  T_Functor_8 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
d__'60''38''62'__80 v0 = coe d__'60''38''62'__28 (coe v0)

-- Haskell.Prim.Functor._.fmap
d_fmap_82 ::
  T_Functor_8 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d_fmap_82 v0 = coe d_fmap_24 (coe v0)

-- Haskell.Prim.Functor._.void
d_void_84 :: T_Functor_8 -> () -> AgdaAny -> AgdaAny
d_void_84 v0 = coe d_void_34 (coe v0)

-- Haskell.Prim.Functor._._$>_
d__'36''62'__94 ::
  (() -> ()) ->
  T_DefaultFunctor_38 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
d__'36''62'__94 ~v0 v1 = du__'36''62'__94 v1
du__'36''62'__94 ::
  T_DefaultFunctor_38 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
du__'36''62'__94 v0 v1 v2 v3 v4 =
  coe du__'36''62'__62 (coe v0) v3 v4

-- Haskell.Prim.Functor._._<$_
d__'60''36'__96 ::
  (() -> ()) ->
  T_DefaultFunctor_38 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d__'60''36'__96 ~v0 v1 = du__'60''36'__96 v1
du__'60''36'__96 ::
  T_DefaultFunctor_38 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
du__'60''36'__96 v0 v1 v2 v3 v4 =
  coe du__'60''36'__54 (coe v0) v3 v4

-- Haskell.Prim.Functor._._<$>_
d__'60''36''62'__98 ::
  (() -> ()) ->
  T_DefaultFunctor_38 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d__'60''36''62'__98 ~v0 v1 = du__'60''36''62'__98 v1
du__'60''36''62'__98 ::
  T_DefaultFunctor_38 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
du__'60''36''62'__98 v0 v1 v2 = coe du__'60''36''62'__46 (coe v0)

-- Haskell.Prim.Functor._._<&>_
d__'60''38''62'__100 ::
  (() -> ()) ->
  T_DefaultFunctor_38 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
d__'60''38''62'__100 ~v0 v1 = du__'60''38''62'__100 v1
du__'60''38''62'__100 ::
  T_DefaultFunctor_38 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
du__'60''38''62'__100 v0 v1 v2 v3 v4 =
  coe du__'60''38''62'__48 (coe v0) v3 v4

-- Haskell.Prim.Functor._.fmap
d_fmap_102 ::
  T_DefaultFunctor_38 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d_fmap_102 v0 = coe d_fmap_44 (coe v0)

-- Haskell.Prim.Functor._.void
d_void_104 ::
  (() -> ()) -> T_DefaultFunctor_38 -> () -> AgdaAny -> AgdaAny
d_void_104 ~v0 v1 = du_void_104 v1
du_void_104 :: T_DefaultFunctor_38 -> () -> AgdaAny -> AgdaAny
du_void_104 v0 v1 = coe du_void_68 (coe v0)

-- Haskell.Prim.Functor.fmap=_
d_fmap'61'__110 ::
  (() -> ()) ->
  (() -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  T_Functor_8
d_fmap'61'__110 ~v0 v1 = du_fmap'61'__110 v1
du_fmap'61'__110 ::
  (() -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  T_Functor_8
du_fmap'61'__110 v0 =
  coe
    C_Functor'46'constructor_585
    (coe v0)
    ( \v1 v2 ->
        coe
          du__'60''36''62'__46
          (coe C_DefaultFunctor'46'constructor_1081 (coe v0))
    )
    ( \v1 v2 v3 v4 ->
        coe
          du__'60''38''62'__48
          (coe C_DefaultFunctor'46'constructor_1081 (coe v0))
          v3
          v4
    )
    ( \v1 v2 v3 v4 ->
        coe
          du__'60''36'__54
          (coe C_DefaultFunctor'46'constructor_1081 (coe v0))
          v3
          v4
    )
    ( \v1 v2 v3 v4 ->
        coe
          du__'36''62'__62
          (coe C_DefaultFunctor'46'constructor_1081 (coe v0))
          v3
          v4
    )
    ( \v1 ->
        coe du_void_68 (coe C_DefaultFunctor'46'constructor_1081 (coe v0))
    )

-- Haskell.Prim.Functor._._$>_
d__'36''62'__118 ::
  (() -> ()) ->
  (() -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
d__'36''62'__118 ~v0 v1 = du__'36''62'__118 v1
du__'36''62'__118 ::
  (() -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
du__'36''62'__118 v0 v1 v2 v3 v4 =
  coe
    du__'36''62'__62
    (coe C_DefaultFunctor'46'constructor_1081 (coe v0))
    v3
    v4

-- Haskell.Prim.Functor._._<$_
d__'60''36'__120 ::
  (() -> ()) ->
  (() -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d__'60''36'__120 ~v0 v1 = du__'60''36'__120 v1
du__'60''36'__120 ::
  (() -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
du__'60''36'__120 v0 v1 v2 v3 v4 =
  coe
    du__'60''36'__54
    (coe C_DefaultFunctor'46'constructor_1081 (coe v0))
    v3
    v4

-- Haskell.Prim.Functor._._<$>_
d__'60''36''62'__122 ::
  (() -> ()) ->
  (() -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d__'60''36''62'__122 ~v0 v1 = du__'60''36''62'__122 v1
du__'60''36''62'__122 ::
  (() -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
du__'60''36''62'__122 v0 v1 v2 =
  coe
    du__'60''36''62'__46
    (coe C_DefaultFunctor'46'constructor_1081 (coe v0))

-- Haskell.Prim.Functor._._<&>_
d__'60''38''62'__124 ::
  (() -> ()) ->
  (() -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
d__'60''38''62'__124 ~v0 v1 = du__'60''38''62'__124 v1
du__'60''38''62'__124 ::
  (() -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
du__'60''38''62'__124 v0 v1 v2 v3 v4 =
  coe
    du__'60''38''62'__48
    (coe C_DefaultFunctor'46'constructor_1081 (coe v0))
    v3
    v4

-- Haskell.Prim.Functor._.void
d_void_128 ::
  (() -> ()) ->
  (() -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  () ->
  AgdaAny ->
  AgdaAny
d_void_128 ~v0 v1 = du_void_128 v1
du_void_128 ::
  (() -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  () ->
  AgdaAny ->
  AgdaAny
du_void_128 v0 v1 =
  coe
    du_void_68
    (coe C_DefaultFunctor'46'constructor_1081 (coe v0))

-- Haskell.Prim.Functor.iFunctorList
d_iFunctorList_130 :: T_Functor_8
d_iFunctorList_130 =
  coe
    du_fmap'61'__110
    ( \v0 v1 v2 v3 ->
        coe MAlonzo.Code.Haskell.Prim.List.du_map_6 v2 v3
    )

-- Haskell.Prim.Functor.iFunctorMaybe
d_iFunctorMaybe_132 :: T_Functor_8
d_iFunctorMaybe_132 =
  coe
    du_fmap'61'__110
    ( coe
        ( \v0 v1 v2 v3 ->
            case coe v3 of
              MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16 -> coe v3
              MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 v4 ->
                coe MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 (coe v2 v4)
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )

-- Haskell.Prim.Functor.iFunctorEither
d_iFunctorEither_142 :: () -> T_Functor_8
d_iFunctorEither_142 ~v0 = du_iFunctorEither_142
du_iFunctorEither_142 :: T_Functor_8
du_iFunctorEither_142 =
  coe
    du_fmap'61'__110
    ( coe
        ( \v0 v1 v2 v3 ->
            case coe v3 of
              MAlonzo.Code.Haskell.Prim.Either.C_Left_16 v4 -> coe v3
              MAlonzo.Code.Haskell.Prim.Either.C_Right_18 v4 ->
                coe MAlonzo.Code.Haskell.Prim.Either.C_Right_18 (coe v2 v4)
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )

-- Haskell.Prim.Functor.iFunctorFun
d_iFunctorFun_156 :: () -> T_Functor_8
d_iFunctorFun_156 ~v0 = du_iFunctorFun_156
du_iFunctorFun_156 :: T_Functor_8
du_iFunctorFun_156 =
  coe
    du_fmap'61'__110
    (coe (\v0 v1 -> coe MAlonzo.Code.Haskell.Prim.du__'8728'__28))

-- Haskell.Prim.Functor.iFunctorTuple₂
d_iFunctorTuple'8322'_160 :: () -> T_Functor_8
d_iFunctorTuple'8322'_160 ~v0 = du_iFunctorTuple'8322'_160
du_iFunctorTuple'8322'_160 :: T_Functor_8
du_iFunctorTuple'8322'_160 =
  coe
    du_fmap'61'__110
    ( coe
        ( \v0 v1 v2 v3 ->
            coe
              MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24
              (coe MAlonzo.Code.Haskell.Prim.Tuple.d_fst_20 (coe v3))
              (coe v2 (MAlonzo.Code.Haskell.Prim.Tuple.d_snd_22 (coe v3)))
        )
    )

-- Haskell.Prim.Functor.iFunctorTuple₃
d_iFunctorTuple'8323'_172 :: () -> () -> T_Functor_8
d_iFunctorTuple'8323'_172 ~v0 ~v1 = du_iFunctorTuple'8323'_172
du_iFunctorTuple'8323'_172 :: T_Functor_8
du_iFunctorTuple'8323'_172 =
  coe
    du_fmap'61'__110
    ( coe
        ( \v0 v1 v2 v3 ->
            case coe v3 of
              MAlonzo.Code.Haskell.Prim.Tuple.C__'44'_'44'__40 v4 v5 v6 ->
                coe
                  MAlonzo.Code.Haskell.Prim.Tuple.C__'44'_'44'__40
                  (coe v4)
                  (coe v5)
                  (coe v2 v6)
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )

-- Haskell.Prim.Functor.iFunctiorIO
d_iFunctiorIO_184 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Prim.Functor.iFunctiorIO"
