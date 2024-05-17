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

module MAlonzo.Code.Peras.Protocol where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.DivMod
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

-- Peras.Protocol.Slot
d_Slot_4 :: ()
d_Slot_4 = erased

-- Peras.Protocol.Round
d_Round_6 :: ()
d_Round_6 = erased

-- Peras.Protocol.Party
d_Party_8 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol.Party"

-- Peras.Protocol.Chain
d_Chain_10 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol.Chain"

-- Peras.Protocol.Block
d_Block_12 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol.Block"

-- Peras.Protocol.Certificate
d_Certificate_14 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol.Certificate"

-- Peras.Protocol.Certify
d_Certify_16 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol.Certify"

-- Peras.Protocol.set
d_set_18 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol.set"

-- Peras.Protocol.singleton
d_singleton_22 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol.singleton"

-- Peras.Protocol.null
d_null_24 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol.null"

-- Peras.Protocol.toList
d_toList_28 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol.toList"

-- Peras.Protocol._isLeaderInSlot_
d__isLeaderInSlot__30 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol._isLeaderInSlot_"

-- Peras.Protocol._trimmedBy_
d__trimmedBy__32 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol._trimmedBy_"

-- Peras.Protocol._isCommitteeMemberInRound_
d__isCommitteeMemberInRound__34 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol._isCommitteeMemberInRound_"

-- Peras.Protocol._pointsInto_
d__pointsInto__36 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol._pointsInto_"

-- Peras.Protocol.length
d_length_38 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol.length"

-- Peras.Protocol.round
d_round_40 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol.round"

-- Peras.Protocol._[_]
d__'91'_'93'_44 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol._[_]"

-- Peras.Protocol._⟦_⟧
d__'10214'_'10215'_46 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol._\10214_\10215"

-- Peras.Protocol._==_
d__'61''61'__50 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol._==_"

-- Peras.Protocol._and_
d__and__52 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol._and_"

-- Peras.Protocol._≤_
d__'8804'__54 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol._\8804_"

-- Peras.Protocol._≥_
d__'8805'__56 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol._\8805_"

-- Peras.Protocol._>_
d__'62'__58 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol._>_"

-- Peras.Protocol._-_
d__'45'__60 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol._-_"

-- Peras.Protocol._/_
d__'47'__62 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol._/_"

-- Peras.Protocol.U
d_U_64 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol.U"

-- Peras.Protocol.A
d_A_66 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol.A"

-- Peras.Protocol.W
d_W_68 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol.W"

-- Peras.Protocol.L
d_L_70 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol.L"

-- Peras.Protocol.B
d_B_72 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol.B"

-- Peras.Protocol.R
d_R_74 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol.R"

-- Peras.Protocol.K
d_K_76 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol.K"

-- Peras.Protocol.Vote
d_Vote_78 = ()
data T_Vote_78 = C_MkVote_80 Integer AgdaAny AgdaAny

-- Peras.Protocol.slot
d_slot_82 :: Integer -> Integer
d_slot_82 v0 = coe d__'47'__62 v0 d_U_64

-- Peras.Protocol.Node
d_Node_86 a0 = ()
data T_Node_86
  = C_bind_92 T_Node_86 (AgdaAny -> T_Node_86)
  | C_ret_96 AgdaAny
  | C_forgeBlock_98 AgdaAny
  | C_preferredChain_100
  | C_preferredVotes_102
  | C_certificates_104
  | C_latestCertificateOnChain_106 AgdaAny
  | C_latestCertificateSeen_108
  | C_mkCertificate_110 Integer AgdaAny
  | C_existsBlockWithQuorum_112 AgdaAny (Maybe AgdaAny -> T_Node_86)
  | C__extendWith__114 AgdaAny AgdaAny
  | C_output_116 AgdaAny
  | C__'58''61'__120 AgdaAny T_Node_86
  | C__'43''61'__124 AgdaAny AgdaAny

-- Peras.Protocol.Monad
d_Monad_128 a0 = ()
data T_Monad_128
  = C_Monad'46'constructor_485
      ( () ->
        () ->
        AgdaAny ->
        (AgdaAny -> AgdaAny) ->
        AgdaAny
      )
      (() -> AgdaAny -> AgdaAny)

-- Peras.Protocol.Monad._>>=_
d__'62''62''61'__146 ::
  T_Monad_128 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
d__'62''62''61'__146 v0 =
  case coe v0 of
    C_Monad'46'constructor_485 v1 v2 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Protocol.Monad.return
d_return_150 :: T_Monad_128 -> () -> AgdaAny -> AgdaAny
d_return_150 v0 =
  case coe v0 of
    C_Monad'46'constructor_485 v1 v2 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Protocol.Monad._>>_
d__'62''62'__156 ::
  (() -> ()) ->
  T_Monad_128 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d__'62''62'__156 ~v0 v1 ~v2 ~v3 v4 v5 = du__'62''62'__156 v1 v4 v5
du__'62''62'__156 :: T_Monad_128 -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__156 v0 v1 v2 =
  coe d__'62''62''61'__146 v0 erased erased v1 (\v3 -> v2)

-- Peras.Protocol.Monad.when
d_when_166 ::
  (() -> ()) -> T_Monad_128 -> () -> Bool -> AgdaAny -> AgdaAny
d_when_166 ~v0 v1 ~v2 v3 v4 = du_when_166 v1 v3 v4
du_when_166 :: T_Monad_128 -> Bool -> AgdaAny -> AgdaAny
du_when_166 v0 v1 v2 =
  coe
    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
    (coe v1)
    ( coe
        du__'62''62'__156
        (coe v0)
        (coe v2)
        ( coe
            d_return_150
            v0
            erased
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
        )
    )
    ( coe
        d_return_150
        v0
        erased
        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
    )

-- Peras.Protocol.NodeMonad
d_NodeMonad_172 :: T_Monad_128
d_NodeMonad_172 =
  coe
    C_Monad'46'constructor_485
    (\v0 v1 v2 v3 -> coe C_bind_92 v2 v3)
    (\v0 v1 -> coe C_ret_96 v1)

-- Peras.Protocol._._>>_
d__'62''62'__176 ::
  (() -> ()) ->
  T_Monad_128 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d__'62''62'__176 ~v0 v1 = du__'62''62'__176 v1
du__'62''62'__176 ::
  T_Monad_128 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__176 v0 v1 v2 v3 v4 =
  coe du__'62''62'__156 (coe v0) v3 v4

-- Peras.Protocol._._>>=_
d__'62''62''61'__178 ::
  T_Monad_128 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
d__'62''62''61'__178 v0 = coe d__'62''62''61'__146 (coe v0)

-- Peras.Protocol._.return
d_return_180 :: T_Monad_128 -> () -> AgdaAny -> AgdaAny
d_return_180 v0 = coe d_return_150 (coe v0)

-- Peras.Protocol._.when
d_when_182 ::
  (() -> ()) -> T_Monad_128 -> () -> Bool -> AgdaAny -> AgdaAny
d_when_182 ~v0 v1 = du_when_182 v1
du_when_182 :: T_Monad_128 -> () -> Bool -> AgdaAny -> AgdaAny
du_when_182 v0 v1 v2 v3 = coe du_when_166 (coe v0) v2 v3

-- Peras.Protocol.Cpref
d_Cpref_184 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol.Cpref"

-- Peras.Protocol.certseen
d_certseen_186 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol.certseen"

-- Peras.Protocol.certchain
d_certchain_188 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol.certchain"

-- Peras.Protocol.Vpref
d_Vpref_190 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol.Vpref"

-- Peras.Protocol.Certs
d_Certs_192 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Protocol.Certs"

-- Peras.Protocol.onNewSlot
d_onNewSlot_194 :: AgdaAny -> Integer -> T_Node_86
d_onNewSlot_194 v0 v1 =
  coe
    du_when_166
    (coe d_NodeMonad_172)
    (coe d__isLeaderInSlot__30 v0 v1)
    ( coe
        d__'62''62''61'__146
        d_NodeMonad_172
        erased
        erased
        (coe C_forgeBlock_98 (coe d_Cpref_184))
        ( \v2 ->
            coe
              du_when_166
              (coe d_NodeMonad_172)
              ( coe
                  MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                  ( coe
                      d__'61''61'__50
                      erased
                      ( coe
                          d__'91'_'93'_44
                          erased
                          d_Certs_192
                          (coe d__'45'__60 (coe d__'47'__62 v1 d_U_64) (2 :: Integer))
                      )
                      d_null_24
                  )
                  ( coe
                      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                      ( coe
                          d__'8804'__54
                          ( coe
                              d__'45'__60
                              (coe d__'47'__62 v1 d_U_64)
                              (coe d_round_40 d_certseen_186)
                          )
                          d_A_66
                      )
                      ( coe
                          d__'62'__58
                          (coe d_round_40 d_certseen_186)
                          (coe d_round_40 d_certchain_188)
                      )
                  )
              )
              ( coe
                  d__'62''62''61'__146
                  d_NodeMonad_172
                  erased
                  erased
                  (coe C__extendWith__114 (coe d_Cpref_184) (coe v2))
                  (\v3 -> coe C_output_116 (coe d__trimmedBy__32 v3 d_W_68))
              )
        )
    )

-- Peras.Protocol.cooldownHasPassed
d_cooldownHasPassed_208 :: Integer -> Bool
d_cooldownHasPassed_208 v0 =
  let v1 = d_K_76
   in coe
        ( case coe v1 of
            0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
            _ ->
              let v2 = subInt (coe d_K_76) (coe (1 :: Integer))
               in coe
                    ( coe
                        MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                        (coe d__'62'__58 (coe d_q_226 v2 v0 erased) (0 :: Integer))
                        ( coe
                            d__'61''61'__50
                            erased
                            (coe d_r_228 v2 v0 erased)
                            (0 :: Integer)
                        )
                    )
        )

-- Peras.Protocol._.q
d_q_226 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  Integer
d_q_226 v0 v1 =
  coe
    MAlonzo.Code.Data.Nat.DivMod.d__div__1096
    v1
    (addInt (coe (1 :: Integer)) (coe v0))

-- Peras.Protocol._.r
d_r_228 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  Integer
d_r_228 v0 v1 v2 =
  coe
    MAlonzo.Code.Data.Nat.Base.du__'37'__326
    (coe v1)
    (coe addInt (coe (1 :: Integer)) (coe v0))

-- Peras.Protocol.voteInRound
d_voteInRound_230 :: AgdaAny -> [AgdaAny] -> Integer -> Bool
d_voteInRound_230 ~v0 ~v1 v2 = du_voteInRound_230 v2
du_voteInRound_230 :: Integer -> Bool
du_voteInRound_230 v0 =
  coe
    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
    ( coe
        MAlonzo.Code.Data.Bool.Base.d__'8743'__24
        ( coe
            d__'61''61'__50
            erased
            (coe d_round_40 d_certseen_186)
            (coe d__'45'__60 v0 (1 :: Integer))
        )
        (coe d__pointsInto__36 d_certseen_186 d_Cpref_184)
    )
    ( coe
        MAlonzo.Code.Data.Bool.Base.d__'8743'__24
        ( coe
            d__'8805'__56
            (coe d__'45'__60 v0 (coe d_round_40 d_certseen_186))
            d_R_74
        )
        ( coe
            d_cooldownHasPassed_208
            (coe d__'45'__60 v0 (coe d_round_40 d_certchain_188))
        )
    )

-- Peras.Protocol.onNewRound
d_onNewRound_238 :: AgdaAny -> Integer -> T_Node_86
d_onNewRound_238 v0 v1 =
  coe
    du_when_166
    (coe d_NodeMonad_172)
    ( coe
        MAlonzo.Code.Data.Bool.Base.d__'8743'__24
        (coe d__isCommitteeMemberInRound__34 v0 v1)
        (coe du_voteInRound_230 (coe v1))
    )
    ( coe
        C__'43''61'__124
        (coe d__'91'_'93'_44 erased d_Vpref_190 v1)
        ( coe
            d_singleton_22
            erased
            ( coe
                C_MkVote_80
                (coe v1)
                (coe v0)
                ( coe
                    d__'10214'_'10215'_46
                    d_Cpref_184
                    (coe d__'45'__60 (d_slot_82 (coe v1)) d_L_70)
                )
            )
        )
    )

-- Peras.Protocol.onPeerVotesChange
d_onPeerVotesChange_244 :: AgdaAny -> Integer -> T_Node_86
d_onPeerVotesChange_244 v0 v1 =
  coe
    du_when_166
    (coe d_NodeMonad_172)
    ( coe
        d__'61''61'__50
        erased
        (coe d__'91'_'93'_44 erased d_Certs_192 v1)
        d_null_24
    )
    ( coe
        du__'62''62'__156
        (coe d_NodeMonad_172)
        ( coe
            C__'43''61'__124
            (coe d__'91'_'93'_44 erased d_Vpref_190 v1)
            v0
        )
        ( coe
            C_existsBlockWithQuorum_112
            (coe d__'91'_'93'_44 erased d_Vpref_190 v1)
            ( coe
                ( \v2 ->
                    case coe v2 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3 ->
                        coe
                          C__'58''61'__120
                          (coe d__'91'_'93'_44 erased d_Certs_192 v1)
                          (coe C_mkCertificate_110 (coe v1) (coe v3))
                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 ->
                        coe
                          d_return_150
                          d_NodeMonad_172
                          erased
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      _ -> MAlonzo.RTE.mazUnreachableError
                )
            )
        )
    )

-- Peras.Protocol.onPeerCertsChange
d_onPeerCertsChange_254 :: AgdaAny -> Integer -> T_Node_86
d_onPeerCertsChange_254 v0 v1 =
  coe
    du_when_166
    (coe d_NodeMonad_172)
    ( coe
        d__'61''61'__50
        erased
        (coe d__'91'_'93'_44 erased d_Certs_192 v1)
        d_null_24
    )
    ( coe
        C__'58''61'__120
        (coe d__'91'_'93'_44 erased d_Certs_192 v1)
        (coe d_return_150 d_NodeMonad_172 erased v0)
    )

-- Peras.Protocol.chainWeight
d_chainWeight_260 :: AgdaAny -> [AgdaAny] -> Integer
d_chainWeight_260 v0 v1 =
  coe
    MAlonzo.Code.Data.List.Base.du_foldr_242
    ( coe
        ( \v2 v3 ->
            coe
              MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
              (coe d__pointsInto__36 v2 v0)
              (coe addInt (coe d_B_72) (coe v3))
              (coe v3)
        )
    )
    (coe d_length_38 v0)
    (coe v1)

-- Peras.Protocol.onPeerChainChange
d_onPeerChainChange_270 :: AgdaAny -> AgdaAny -> T_Node_86
d_onPeerChainChange_270 v0 ~v1 = du_onPeerChainChange_270 v0
du_onPeerChainChange_270 :: AgdaAny -> T_Node_86
du_onPeerChainChange_270 v0 =
  coe
    du__'62''62'__156
    (coe d_NodeMonad_172)
    ( coe
        du_when_166
        (coe d_NodeMonad_172)
        ( coe
            d__'62'__58
            (d_chainWeight_260 (coe v0) (coe d_Certs_192))
            (d_chainWeight_260 (coe d_Cpref_184) (coe d_Certs_192))
        )
        ( coe
            C__'58''61'__120
            d_Cpref_184
            (coe d_return_150 d_NodeMonad_172 erased v0)
        )
    )
    (coe C_output_116 (coe d__trimmedBy__32 d_Cpref_184 d_W_68))
