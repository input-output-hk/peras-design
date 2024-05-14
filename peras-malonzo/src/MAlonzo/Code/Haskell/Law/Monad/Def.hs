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

module MAlonzo.Code.Haskell.Law.Monad.Def where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Haskell.Law.Applicative.Def
import qualified MAlonzo.Code.Haskell.Prim.Monad
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

-- Haskell.Law.Monad.Def.IsLawfulMonad
d_IsLawfulMonad_12 a0 a1 = ()
data T_IsLawfulMonad_12 = C_IsLawfulMonad'46'constructor_15853

-- Haskell.Law.Monad.Def.IsLawfulMonad.super
d_super_84 ::
  T_IsLawfulMonad_12 ->
  MAlonzo.Code.Haskell.Law.Applicative.Def.T_IsLawfulApplicative_12
d_super_84 = erased

-- Haskell.Law.Monad.Def.IsLawfulMonad.leftIdentity
d_leftIdentity_92 ::
  T_IsLawfulMonad_12 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftIdentity_92 = erased

-- Haskell.Law.Monad.Def.IsLawfulMonad.rightIdentity
d_rightIdentity_98 ::
  T_IsLawfulMonad_12 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightIdentity_98 = erased

-- Haskell.Law.Monad.Def.IsLawfulMonad.associativity
d_associativity_114 ::
  T_IsLawfulMonad_12 ->
  () ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_associativity_114 = erased

-- Haskell.Law.Monad.Def.IsLawfulMonad.pureIsReturn
d_pureIsReturn_118 ::
  T_IsLawfulMonad_12 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pureIsReturn_118 = erased

-- Haskell.Law.Monad.Def.IsLawfulMonad.sequence2bind
d_sequence2bind_132 ::
  T_IsLawfulMonad_12 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sequence2bind_132 = erased

-- Haskell.Law.Monad.Def.IsLawfulMonad.fmap2bind
d_fmap2bind_142 ::
  T_IsLawfulMonad_12 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap2bind_142 = erased

-- Haskell.Law.Monad.Def.IsLawfulMonad.rSequence2rBind
d_rSequence2rBind_148 ::
  T_IsLawfulMonad_12 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rSequence2rBind_148 = erased

-- Haskell.Law.Monad.Def._.associativity
d_associativity_152 ::
  T_IsLawfulMonad_12 ->
  () ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_associativity_152 = erased

-- Haskell.Law.Monad.Def._.fmap2bind
d_fmap2bind_154 ::
  T_IsLawfulMonad_12 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap2bind_154 = erased

-- Haskell.Law.Monad.Def._.leftIdentity
d_leftIdentity_156 ::
  T_IsLawfulMonad_12 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftIdentity_156 = erased

-- Haskell.Law.Monad.Def._.pureIsReturn
d_pureIsReturn_158 ::
  T_IsLawfulMonad_12 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pureIsReturn_158 = erased

-- Haskell.Law.Monad.Def._.rSequence2rBind
d_rSequence2rBind_160 ::
  T_IsLawfulMonad_12 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rSequence2rBind_160 = erased

-- Haskell.Law.Monad.Def._.rightIdentity
d_rightIdentity_162 ::
  T_IsLawfulMonad_12 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightIdentity_162 = erased

-- Haskell.Law.Monad.Def._.sequence2bind
d_sequence2bind_164 ::
  T_IsLawfulMonad_12 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sequence2bind_164 = erased

-- Haskell.Law.Monad.Def._.super
d_super_166 ::
  T_IsLawfulMonad_12 ->
  MAlonzo.Code.Haskell.Law.Applicative.Def.T_IsLawfulApplicative_12
d_super_166 = erased

-- Haskell.Law.Monad.Def.iLawfulMonadFun
d_iLawfulMonadFun_170 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Monad.Def.iLawfulMonadFun"

-- Haskell.Law.Monad.Def.iLawfulMonadTuple₂
d_iLawfulMonadTuple'8322'_174 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Monad.Def.iLawfulMonadTuple\8322"

-- Haskell.Law.Monad.Def.iLawfulMonadTuple₃
d_iLawfulMonadTuple'8323'_178 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Monad.Def.iLawfulMonadTuple\8323"
