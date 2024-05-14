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

module MAlonzo.Code.Haskell.Law.List where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Haskell.Prim
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

-- Haskell.Law.List.[]≠∷
d_'91''93''8800''8759'_10 ::
  () ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Haskell.Prim.T_'8869'_90
d_'91''93''8800''8759'_10 = erased

-- Haskell.Law.List._.∷-injective-left
d_'8759''45'injective'45'left_30 ::
  () ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8759''45'injective'45'left_30 = erased

-- Haskell.Law.List._.∷-injective-right
d_'8759''45'injective'45'right_32 ::
  () ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8759''45'injective'45'right_32 = erased

-- Haskell.Law.List.map-id
d_map'45'id_36 ::
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'id_36 = erased

-- Haskell.Law.List.map-++
d_map'45''43''43'_50 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45''43''43'_50 = erased

-- Haskell.Law.List.lengthMap
d_lengthMap_70 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lengthMap_70 = erased

-- Haskell.Law.List.map-∘
d_map'45''8728'_86 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45''8728'_86 = erased

-- Haskell.Law.List.lengthNat-++
d_lengthNat'45''43''43'_106 ::
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lengthNat'45''43''43'_106 = erased

-- Haskell.Law.List.++-[]
d_'43''43''45''91''93'_114 ::
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''43''45''91''93'_114 = erased

-- Haskell.Law.List.[]-++
d_'91''93''45''43''43'_126 ::
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'91''93''45''43''43'_126 = erased

-- Haskell.Law.List.++-assoc
d_'43''43''45'assoc_136 ::
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''43''45'assoc_136 = erased

-- Haskell.Law.List.++-∷-assoc
d_'43''43''45''8759''45'assoc_160 ::
  () ->
  [AgdaAny] ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''43''45''8759''45'assoc_160 = erased

-- Haskell.Law.List.∷-++-assoc
d_'8759''45''43''43''45'assoc_182 ::
  () ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8759''45''43''43''45'assoc_182 = erased

-- Haskell.Law.List.++-identity-right-unique
d_'43''43''45'identity'45'right'45'unique_194 ::
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''43''45'identity'45'right'45'unique_194 = erased

-- Haskell.Law.List.++-identity-left-unique
d_'43''43''45'identity'45'left'45'unique_206 ::
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''43''45'identity'45'left'45'unique_206 = erased

-- Haskell.Law.List.++-cancel-left
d_'43''43''45'cancel'45'left_244 ::
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''43''45'cancel'45'left_244 = erased

-- Haskell.Law.List.++-cancel-right
d_'43''43''45'cancel'45'right_264 ::
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''43''45'cancel'45'right_264 = erased

-- Haskell.Law.List.++-conical-left
d_'43''43''45'conical'45'left_300 ::
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''43''45'conical'45'left_300 = erased

-- Haskell.Law.List.++-conical-right
d_'43''43''45'conical'45'right_306 ::
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''43''45'conical'45'right_306 = erased

-- Haskell.Law.List.∷-not-identity
d_'8759''45'not'45'identity_314 ::
  () ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Haskell.Prim.T_'8869'_90
d_'8759''45'not'45'identity_314 = erased

-- Haskell.Law.List.foldr-universal
d_foldr'45'universal_336 ::
  () ->
  () ->
  ([AgdaAny] -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ( AgdaAny ->
    [AgdaAny] ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
  ) ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_foldr'45'universal_336 = erased

-- Haskell.Law.List.foldr-cong
d_foldr'45'cong_380 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  ( AgdaAny ->
    AgdaAny ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
  ) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_foldr'45'cong_380 = erased

-- Haskell.Law.List.foldr-fusion
d_foldr'45'fusion_412 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  ( AgdaAny ->
    AgdaAny ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
  ) ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_foldr'45'fusion_412 = erased
