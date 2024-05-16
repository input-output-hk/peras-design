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

module MAlonzo.Code.Haskell.Prim.Traversable where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Haskell.Prim.Applicative
import qualified MAlonzo.Code.Haskell.Prim.Either
import qualified MAlonzo.Code.Haskell.Prim.Foldable
import qualified MAlonzo.Code.Haskell.Prim.Functor
import qualified MAlonzo.Code.Haskell.Prim.List
import qualified MAlonzo.Code.Haskell.Prim.Maybe
import qualified MAlonzo.Code.Haskell.Prim.Monad
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

-- Haskell.Prim.Traversable.Traversable
d_Traversable_8 a0 = ()
data T_Traversable_8
  = C_Traversable'46'constructor_555
      ( (() -> ()) ->
        () ->
        () ->
        MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
        (AgdaAny -> AgdaAny) ->
        AgdaAny ->
        AgdaAny
      )
      MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8
      MAlonzo.Code.Haskell.Prim.Foldable.T_Foldable_8
      ( (() -> ()) ->
        () ->
        MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
        AgdaAny ->
        AgdaAny
      )
      ( (() -> ()) ->
        () ->
        () ->
        MAlonzo.Code.Haskell.Prim.Monad.T_Monad_10 ->
        (AgdaAny -> AgdaAny) ->
        AgdaAny ->
        AgdaAny
      )
      ( (() -> ()) ->
        () ->
        MAlonzo.Code.Haskell.Prim.Monad.T_Monad_10 ->
        AgdaAny ->
        AgdaAny
      )

-- Haskell.Prim.Traversable.Traversable.traverse
d_traverse_24 ::
  T_Traversable_8 ->
  (() -> ()) ->
  () ->
  () ->
  MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d_traverse_24 v0 =
  case coe v0 of
    C_Traversable'46'constructor_555 v1 v2 v3 v4 v5 v6 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Traversable.Traversable.functor
d_functor_26 ::
  T_Traversable_8 -> MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8
d_functor_26 v0 =
  case coe v0 of
    C_Traversable'46'constructor_555 v1 v2 v3 v4 v5 v6 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Traversable.Traversable.foldable
d_foldable_28 ::
  T_Traversable_8 -> MAlonzo.Code.Haskell.Prim.Foldable.T_Foldable_8
d_foldable_28 v0 =
  case coe v0 of
    C_Traversable'46'constructor_555 v1 v2 v3 v4 v5 v6 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Traversable.Traversable.sequenceA
d_sequenceA_30 ::
  T_Traversable_8 ->
  (() -> ()) ->
  () ->
  MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
  AgdaAny ->
  AgdaAny
d_sequenceA_30 v0 =
  case coe v0 of
    C_Traversable'46'constructor_555 v1 v2 v3 v4 v5 v6 -> coe v4
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Traversable.Traversable.mapM
d_mapM_32 ::
  T_Traversable_8 ->
  (() -> ()) ->
  () ->
  () ->
  MAlonzo.Code.Haskell.Prim.Monad.T_Monad_10 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d_mapM_32 v0 =
  case coe v0 of
    C_Traversable'46'constructor_555 v1 v2 v3 v4 v5 v6 -> coe v5
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Traversable.Traversable.sequence
d_sequence_34 ::
  T_Traversable_8 ->
  (() -> ()) ->
  () ->
  MAlonzo.Code.Haskell.Prim.Monad.T_Monad_10 ->
  AgdaAny ->
  AgdaAny
d_sequence_34 v0 =
  case coe v0 of
    C_Traversable'46'constructor_555 v1 v2 v3 v4 v5 v6 -> coe v6
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Traversable.DefaultTraversable
d_DefaultTraversable_38 a0 = ()
data T_DefaultTraversable_38
  = C_DefaultTraversable'46'constructor_1055
      ( (() -> ()) ->
        () ->
        () ->
        MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
        (AgdaAny -> AgdaAny) ->
        AgdaAny ->
        AgdaAny
      )
      MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8
      MAlonzo.Code.Haskell.Prim.Foldable.T_Foldable_8

-- Haskell.Prim.Traversable.DefaultTraversable.traverse
d_traverse_48 ::
  T_DefaultTraversable_38 ->
  (() -> ()) ->
  () ->
  () ->
  MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d_traverse_48 v0 =
  case coe v0 of
    C_DefaultTraversable'46'constructor_1055 v1 v2 v3 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Traversable.DefaultTraversable.functor
d_functor_50 ::
  T_DefaultTraversable_38 ->
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8
d_functor_50 v0 =
  case coe v0 of
    C_DefaultTraversable'46'constructor_1055 v1 v2 v3 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Traversable.DefaultTraversable.foldable
d_foldable_52 ::
  T_DefaultTraversable_38 ->
  MAlonzo.Code.Haskell.Prim.Foldable.T_Foldable_8
d_foldable_52 v0 =
  case coe v0 of
    C_DefaultTraversable'46'constructor_1055 v1 v2 v3 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Traversable.DefaultTraversable.sequenceA
d_sequenceA_54 ::
  (() -> ()) ->
  T_DefaultTraversable_38 ->
  (() -> ()) ->
  () ->
  MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
  AgdaAny ->
  AgdaAny
d_sequenceA_54 ~v0 v1 ~v2 ~v3 v4 = du_sequenceA_54 v1 v4
du_sequenceA_54 ::
  T_DefaultTraversable_38 ->
  MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
  AgdaAny ->
  AgdaAny
du_sequenceA_54 v0 v1 =
  coe d_traverse_48 v0 erased erased erased v1 (\v2 -> v2)

-- Haskell.Prim.Traversable.DefaultTraversable.mapM
d_mapM_56 ::
  (() -> ()) ->
  T_DefaultTraversable_38 ->
  (() -> ()) ->
  () ->
  () ->
  MAlonzo.Code.Haskell.Prim.Monad.T_Monad_10 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d_mapM_56 ~v0 v1 ~v2 ~v3 ~v4 v5 = du_mapM_56 v1 v5
du_mapM_56 ::
  T_DefaultTraversable_38 ->
  MAlonzo.Code.Haskell.Prim.Monad.T_Monad_10 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
du_mapM_56 v0 v1 =
  coe
    d_traverse_48
    v0
    erased
    erased
    erased
    (MAlonzo.Code.Haskell.Prim.Monad.d_super_26 (coe v1))

-- Haskell.Prim.Traversable.DefaultTraversable.sequence
d_sequence_58 ::
  (() -> ()) ->
  T_DefaultTraversable_38 ->
  (() -> ()) ->
  () ->
  MAlonzo.Code.Haskell.Prim.Monad.T_Monad_10 ->
  AgdaAny ->
  AgdaAny
d_sequence_58 ~v0 v1 ~v2 ~v3 v4 = du_sequence_58 v1 v4
du_sequence_58 ::
  T_DefaultTraversable_38 ->
  MAlonzo.Code.Haskell.Prim.Monad.T_Monad_10 ->
  AgdaAny ->
  AgdaAny
du_sequence_58 v0 v1 =
  coe
    du_sequenceA_54
    (coe v0)
    (coe MAlonzo.Code.Haskell.Prim.Monad.d_super_26 (coe v1))

-- Haskell.Prim.Traversable._.foldable
d_foldable_62 ::
  T_Traversable_8 -> MAlonzo.Code.Haskell.Prim.Foldable.T_Foldable_8
d_foldable_62 v0 = coe d_foldable_28 (coe v0)

-- Haskell.Prim.Traversable._.functor
d_functor_64 ::
  T_Traversable_8 -> MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8
d_functor_64 v0 = coe d_functor_26 (coe v0)

-- Haskell.Prim.Traversable._.mapM
d_mapM_66 ::
  T_Traversable_8 ->
  (() -> ()) ->
  () ->
  () ->
  MAlonzo.Code.Haskell.Prim.Monad.T_Monad_10 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d_mapM_66 v0 = coe d_mapM_32 (coe v0)

-- Haskell.Prim.Traversable._.sequence
d_sequence_68 ::
  T_Traversable_8 ->
  (() -> ()) ->
  () ->
  MAlonzo.Code.Haskell.Prim.Monad.T_Monad_10 ->
  AgdaAny ->
  AgdaAny
d_sequence_68 v0 = coe d_sequence_34 (coe v0)

-- Haskell.Prim.Traversable._.sequenceA
d_sequenceA_70 ::
  T_Traversable_8 ->
  (() -> ()) ->
  () ->
  MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
  AgdaAny ->
  AgdaAny
d_sequenceA_70 v0 = coe d_sequenceA_30 (coe v0)

-- Haskell.Prim.Traversable._.traverse
d_traverse_72 ::
  T_Traversable_8 ->
  (() -> ()) ->
  () ->
  () ->
  MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d_traverse_72 v0 = coe d_traverse_24 (coe v0)

-- Haskell.Prim.Traversable._.foldable
d_foldable_82 ::
  T_DefaultTraversable_38 ->
  MAlonzo.Code.Haskell.Prim.Foldable.T_Foldable_8
d_foldable_82 v0 = coe d_foldable_52 (coe v0)

-- Haskell.Prim.Traversable._.functor
d_functor_84 ::
  T_DefaultTraversable_38 ->
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8
d_functor_84 v0 = coe d_functor_50 (coe v0)

-- Haskell.Prim.Traversable._.mapM
d_mapM_86 ::
  (() -> ()) ->
  T_DefaultTraversable_38 ->
  (() -> ()) ->
  () ->
  () ->
  MAlonzo.Code.Haskell.Prim.Monad.T_Monad_10 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d_mapM_86 ~v0 v1 = du_mapM_86 v1
du_mapM_86 ::
  T_DefaultTraversable_38 ->
  (() -> ()) ->
  () ->
  () ->
  MAlonzo.Code.Haskell.Prim.Monad.T_Monad_10 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
du_mapM_86 v0 v1 v2 v3 v4 = coe du_mapM_56 (coe v0) v4

-- Haskell.Prim.Traversable._.sequence
d_sequence_88 ::
  (() -> ()) ->
  T_DefaultTraversable_38 ->
  (() -> ()) ->
  () ->
  MAlonzo.Code.Haskell.Prim.Monad.T_Monad_10 ->
  AgdaAny ->
  AgdaAny
d_sequence_88 ~v0 v1 = du_sequence_88 v1
du_sequence_88 ::
  T_DefaultTraversable_38 ->
  (() -> ()) ->
  () ->
  MAlonzo.Code.Haskell.Prim.Monad.T_Monad_10 ->
  AgdaAny ->
  AgdaAny
du_sequence_88 v0 v1 v2 v3 = coe du_sequence_58 (coe v0) v3

-- Haskell.Prim.Traversable._.sequenceA
d_sequenceA_90 ::
  (() -> ()) ->
  T_DefaultTraversable_38 ->
  (() -> ()) ->
  () ->
  MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
  AgdaAny ->
  AgdaAny
d_sequenceA_90 ~v0 v1 = du_sequenceA_90 v1
du_sequenceA_90 ::
  T_DefaultTraversable_38 ->
  (() -> ()) ->
  () ->
  MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
  AgdaAny ->
  AgdaAny
du_sequenceA_90 v0 v1 v2 v3 = coe du_sequenceA_54 (coe v0) v3

-- Haskell.Prim.Traversable._.traverse
d_traverse_92 ::
  T_DefaultTraversable_38 ->
  (() -> ()) ->
  () ->
  () ->
  MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d_traverse_92 v0 = coe d_traverse_48 (coe v0)

-- Haskell.Prim.Traversable.traverse=_
d_traverse'61'__100 ::
  (() -> ()) ->
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  MAlonzo.Code.Haskell.Prim.Foldable.T_Foldable_8 ->
  ( (() -> ()) ->
    () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  T_Traversable_8
d_traverse'61'__100 ~v0 v1 v2 v3 = du_traverse'61'__100 v1 v2 v3
du_traverse'61'__100 ::
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  MAlonzo.Code.Haskell.Prim.Foldable.T_Foldable_8 ->
  ( (() -> ()) ->
    () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  T_Traversable_8
du_traverse'61'__100 v0 v1 v2 =
  coe
    C_Traversable'46'constructor_555
    (coe v2)
    (coe v0)
    (coe v1)
    ( \v3 v4 v5 ->
        coe
          du_sequenceA_54
          ( coe
              C_DefaultTraversable'46'constructor_1055
              (coe v2)
              (coe v0)
              (coe v1)
          )
          v5
    )
    ( \v3 v4 v5 v6 ->
        coe
          du_mapM_56
          ( coe
              C_DefaultTraversable'46'constructor_1055
              (coe v2)
              (coe v0)
              (coe v1)
          )
          v6
    )
    ( \v3 v4 v5 ->
        coe
          du_sequence_58
          ( coe
              C_DefaultTraversable'46'constructor_1055
              (coe v2)
              (coe v0)
              (coe v1)
          )
          v5
    )

-- Haskell.Prim.Traversable._.mapM
d_mapM_112 ::
  (() -> ()) ->
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  MAlonzo.Code.Haskell.Prim.Foldable.T_Foldable_8 ->
  ( (() -> ()) ->
    () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  (() -> ()) ->
  () ->
  () ->
  MAlonzo.Code.Haskell.Prim.Monad.T_Monad_10 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d_mapM_112 ~v0 v1 v2 v3 = du_mapM_112 v1 v2 v3
du_mapM_112 ::
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  MAlonzo.Code.Haskell.Prim.Foldable.T_Foldable_8 ->
  ( (() -> ()) ->
    () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  (() -> ()) ->
  () ->
  () ->
  MAlonzo.Code.Haskell.Prim.Monad.T_Monad_10 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
du_mapM_112 v0 v1 v2 v3 v4 v5 v6 =
  coe
    du_mapM_56
    ( coe
        C_DefaultTraversable'46'constructor_1055
        (coe v2)
        (coe v0)
        (coe v1)
    )
    v6

-- Haskell.Prim.Traversable._.sequence
d_sequence_114 ::
  (() -> ()) ->
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  MAlonzo.Code.Haskell.Prim.Foldable.T_Foldable_8 ->
  ( (() -> ()) ->
    () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  (() -> ()) ->
  () ->
  MAlonzo.Code.Haskell.Prim.Monad.T_Monad_10 ->
  AgdaAny ->
  AgdaAny
d_sequence_114 ~v0 v1 v2 v3 = du_sequence_114 v1 v2 v3
du_sequence_114 ::
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  MAlonzo.Code.Haskell.Prim.Foldable.T_Foldable_8 ->
  ( (() -> ()) ->
    () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  (() -> ()) ->
  () ->
  MAlonzo.Code.Haskell.Prim.Monad.T_Monad_10 ->
  AgdaAny ->
  AgdaAny
du_sequence_114 v0 v1 v2 v3 v4 v5 =
  coe
    du_sequence_58
    ( coe
        C_DefaultTraversable'46'constructor_1055
        (coe v2)
        (coe v0)
        (coe v1)
    )
    v5

-- Haskell.Prim.Traversable._.sequenceA
d_sequenceA_116 ::
  (() -> ()) ->
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  MAlonzo.Code.Haskell.Prim.Foldable.T_Foldable_8 ->
  ( (() -> ()) ->
    () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  (() -> ()) ->
  () ->
  MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
  AgdaAny ->
  AgdaAny
d_sequenceA_116 ~v0 v1 v2 v3 = du_sequenceA_116 v1 v2 v3
du_sequenceA_116 ::
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  MAlonzo.Code.Haskell.Prim.Foldable.T_Foldable_8 ->
  ( (() -> ()) ->
    () ->
    () ->
    MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
    (AgdaAny -> AgdaAny) ->
    AgdaAny ->
    AgdaAny
  ) ->
  (() -> ()) ->
  () ->
  MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
  AgdaAny ->
  AgdaAny
du_sequenceA_116 v0 v1 v2 v3 v4 v5 =
  coe
    du_sequenceA_54
    ( coe
        C_DefaultTraversable'46'constructor_1055
        (coe v2)
        (coe v0)
        (coe v1)
    )
    v5

-- Haskell.Prim.Traversable.iTraversableList
d_iTraversableList_120 :: T_Traversable_8
d_iTraversableList_120 =
  coe
    du_traverse'61'__100
    ( coe
        MAlonzo.Code.Haskell.Prim.Functor.du_fmap'61'__110
        ( \v0 v1 v2 v3 ->
            coe MAlonzo.Code.Haskell.Prim.List.du_map_6 v2 v3
        )
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.Foldable.du_foldMap'61'__328
        ( \v0 v1 v2 v3 v4 ->
            coe
              MAlonzo.Code.Haskell.Prim.Foldable.du_foldMapList_408
              v2
              v3
              v4
        )
    )
    (\v0 v1 v2 v3 v4 v5 -> coe du_traverseList_126 v3 v4 v5)

-- Haskell.Prim.Traversable._.traverseList
d_traverseList_126 ::
  (() -> ()) ->
  () ->
  () ->
  MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  AgdaAny
d_traverseList_126 ~v0 ~v1 ~v2 v3 v4 v5 =
  du_traverseList_126 v3 v4 v5
du_traverseList_126 ::
  MAlonzo.Code.Haskell.Prim.Applicative.T_Applicative_8 ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  AgdaAny
du_traverseList_126 v0 v1 v2 =
  case coe v2 of
    [] ->
      coe MAlonzo.Code.Haskell.Prim.Applicative.d_pure_22 v0 erased v2
    (:) v3 v4 ->
      coe
        MAlonzo.Code.Haskell.Prim.Applicative.d__'60''42''62'__24
        v0
        erased
        erased
        ( coe
            MAlonzo.Code.Haskell.Prim.Applicative.d__'60''42''62'__24
            v0
            erased
            erased
            ( coe
                MAlonzo.Code.Haskell.Prim.Applicative.d_pure_22
                v0
                erased
                (coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22)
            )
            (coe v1 v3)
        )
        (coe du_traverseList_126 (coe v0) (coe v1) (coe v4))
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Traversable.iTraversableMaybe
d_iTraversableMaybe_136 :: T_Traversable_8
d_iTraversableMaybe_136 =
  coe
    du_traverse'61'__100
    ( coe
        MAlonzo.Code.Haskell.Prim.Functor.du_fmap'61'__110
        ( coe
            ( \v0 v1 v2 v3 ->
                case coe v3 of
                  MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16 -> coe v3
                  MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 v4 ->
                    coe MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 (coe v2 v4)
                  _ -> MAlonzo.RTE.mazUnreachableError
            )
        )
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.Foldable.du_foldMap'61'__328
        ( coe
            ( \v0 v1 v2 v3 v4 ->
                case coe v4 of
                  MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16 ->
                    coe MAlonzo.Code.Haskell.Prim.Monoid.d_mempty_86 (coe v2)
                  MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 v5 -> coe v3 v5
                  _ -> MAlonzo.RTE.mazUnreachableError
            )
        )
    )
    ( coe
        ( \v0 v1 v2 v3 v4 v5 ->
            case coe v5 of
              MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16 ->
                coe MAlonzo.Code.Haskell.Prim.Applicative.d_pure_22 v3 erased v5
              MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 v6 ->
                coe
                  MAlonzo.Code.Haskell.Prim.Functor.d__'60''36''62'__26
                  (MAlonzo.Code.Haskell.Prim.Applicative.d_super_26 (coe v3))
                  erased
                  erased
                  (coe MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18)
                  (coe v4 v6)
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )

-- Haskell.Prim.Traversable.iTraversableEither
d_iTraversableEither_146 :: () -> T_Traversable_8
d_iTraversableEither_146 ~v0 = du_iTraversableEither_146
du_iTraversableEither_146 :: T_Traversable_8
du_iTraversableEither_146 =
  coe
    du_traverse'61'__100
    ( coe
        MAlonzo.Code.Haskell.Prim.Functor.du_fmap'61'__110
        ( coe
            ( \v0 v1 v2 v3 ->
                case coe v3 of
                  MAlonzo.Code.Haskell.Prim.Either.C_Left_16 v4 -> coe v3
                  MAlonzo.Code.Haskell.Prim.Either.C_Right_18 v4 ->
                    coe MAlonzo.Code.Haskell.Prim.Either.C_Right_18 (coe v2 v4)
                  _ -> MAlonzo.RTE.mazUnreachableError
            )
        )
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.Foldable.du_foldMap'61'__328
        ( coe
            ( \v0 v1 v2 v3 v4 ->
                case coe v4 of
                  MAlonzo.Code.Haskell.Prim.Either.C_Left_16 v5 ->
                    coe MAlonzo.Code.Haskell.Prim.Monoid.d_mempty_86 (coe v2)
                  MAlonzo.Code.Haskell.Prim.Either.C_Right_18 v5 -> coe v3 v5
                  _ -> MAlonzo.RTE.mazUnreachableError
            )
        )
    )
    ( coe
        ( \v0 v1 v2 v3 v4 v5 ->
            case coe v5 of
              MAlonzo.Code.Haskell.Prim.Either.C_Left_16 v6 ->
                coe MAlonzo.Code.Haskell.Prim.Applicative.d_pure_22 v3 erased v5
              MAlonzo.Code.Haskell.Prim.Either.C_Right_18 v6 ->
                coe
                  MAlonzo.Code.Haskell.Prim.Functor.d__'60''36''62'__26
                  (MAlonzo.Code.Haskell.Prim.Applicative.d_super_26 (coe v3))
                  erased
                  erased
                  (coe MAlonzo.Code.Haskell.Prim.Either.C_Right_18)
                  (coe v4 v6)
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )

-- Haskell.Prim.Traversable.iTraversablePair
d_iTraversablePair_160 :: () -> T_Traversable_8
d_iTraversablePair_160 ~v0 = du_iTraversablePair_160
du_iTraversablePair_160 :: T_Traversable_8
du_iTraversablePair_160 =
  coe
    du_traverse'61'__100
    ( coe
        MAlonzo.Code.Haskell.Prim.Functor.du_fmap'61'__110
        ( coe
            ( \v0 v1 v2 v3 ->
                coe
                  MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24
                  (coe MAlonzo.Code.Haskell.Prim.Tuple.d_fst_20 (coe v3))
                  (coe v2 (MAlonzo.Code.Haskell.Prim.Tuple.d_snd_22 (coe v3)))
            )
        )
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.Foldable.du_foldMap'61'__328
        ( coe
            ( \v0 v1 v2 v3 v4 ->
                coe v3 (MAlonzo.Code.Haskell.Prim.Tuple.d_snd_22 (coe v4))
            )
        )
    )
    ( coe
        ( \v0 v1 v2 v3 v4 v5 ->
            coe
              MAlonzo.Code.Haskell.Prim.Functor.d__'60''36''62'__26
              (MAlonzo.Code.Haskell.Prim.Applicative.d_super_26 (coe v3))
              erased
              erased
              ( \v6 ->
                  coe
                    MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24
                    (coe MAlonzo.Code.Haskell.Prim.Tuple.d_fst_20 (coe v5))
                    (coe v6)
              )
              (coe v4 (MAlonzo.Code.Haskell.Prim.Tuple.d_snd_22 (coe v5)))
        )
    )
