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

module MAlonzo.Code.Peras.ProtocolL where

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

-- Peras.ProtocolL._[_]
d__'91'_'93'_6 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL._[_]"

-- Peras.ProtocolL._==_
d__'61''61'__10 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL._==_"

-- Peras.ProtocolL._and_
d__and__12 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL._and_"

-- Peras.ProtocolL._≤_
d__'8804'__14 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL._\8804_"

-- Peras.ProtocolL._≥_
d__'8805'__16 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL._\8805_"

-- Peras.ProtocolL._>_
d__'62'__18 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL._>_"

-- Peras.ProtocolL._-_
d__'45'__20 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL._-_"

-- Peras.ProtocolL._/_
d__'47'__22 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL._/_"

-- Peras.ProtocolL.set
d_set_24 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL.set"

-- Peras.ProtocolL.singleton
d_singleton_28 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL.singleton"

-- Peras.ProtocolL.toList
d_toList_32 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL.toList"

-- Peras.ProtocolL.U
d_U_34 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL.U"

-- Peras.ProtocolL.A
d_A_36 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL.A"

-- Peras.ProtocolL.W
d_W_38 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL.W"

-- Peras.ProtocolL.L
d_L_40 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL.L"

-- Peras.ProtocolL.B
d_B_42 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL.B"

-- Peras.ProtocolL.τ
d_τ_44 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL.\964"

-- Peras.ProtocolL.R
d_R_46 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL.R"

-- Peras.ProtocolL.K
d_K_48 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL.K"

-- Peras.ProtocolL.Slot
d_Slot_50 :: ()
d_Slot_50 = erased

-- Peras.ProtocolL.Round
d_Round_52 :: ()
d_Round_52 = erased

-- Peras.ProtocolL.slot
d_slot_54 :: Integer -> Integer
d_slot_54 v0 = coe d__'47'__22 v0 d_U_34

-- Peras.ProtocolL.Party
d_Party_58 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL.Party"

-- Peras.ProtocolL.Hash
d_Hash_60 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL.Hash"

-- Peras.ProtocolL.Proof
d_Proof_62 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL.Proof"

-- Peras.ProtocolL.Payload
d_Payload_64 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL.Payload"

-- Peras.ProtocolL.Signature
d_Signature_66 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL.Signature"

-- Peras.ProtocolL.Certificate
d_Certificate_68 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL.Certificate"

-- Peras.ProtocolL.Block
d_Block_70 = ()
data T_Block_70
  = C_MkBlock_100
      Integer
      AgdaAny
      AgdaAny
      AgdaAny
      AgdaAny
      AgdaAny
      AgdaAny

-- Peras.ProtocolL.Block.slot_number
d_slot_number_86 :: T_Block_70 -> Integer
d_slot_number_86 v0 =
  case coe v0 of
    C_MkBlock_100 v1 v2 v3 v4 v5 v6 v7 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.ProtocolL.Block.creator_ID
d_creator_ID_88 :: T_Block_70 -> AgdaAny
d_creator_ID_88 v0 =
  case coe v0 of
    C_MkBlock_100 v1 v2 v3 v4 v5 v6 v7 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.ProtocolL.Block.hash_of_parent_block
d_hash_of_parent_block_90 :: T_Block_70 -> AgdaAny
d_hash_of_parent_block_90 v0 =
  case coe v0 of
    C_MkBlock_100 v1 v2 v3 v4 v5 v6 v7 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.ProtocolL.Block.certificate
d_certificate_92 :: T_Block_70 -> AgdaAny
d_certificate_92 v0 =
  case coe v0 of
    C_MkBlock_100 v1 v2 v3 v4 v5 v6 v7 -> coe v4
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.ProtocolL.Block.slot-leadership_proof
d_slot'45'leadership_proof_94 :: T_Block_70 -> AgdaAny
d_slot'45'leadership_proof_94 v0 =
  case coe v0 of
    C_MkBlock_100 v1 v2 v3 v4 v5 v6 v7 -> coe v5
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.ProtocolL.Block.payload
d_payload_96 :: T_Block_70 -> AgdaAny
d_payload_96 v0 =
  case coe v0 of
    C_MkBlock_100 v1 v2 v3 v4 v5 v6 v7 -> coe v6
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.ProtocolL.Block.signature
d_signature_98 :: T_Block_70 -> AgdaAny
d_signature_98 v0 =
  case coe v0 of
    C_MkBlock_100 v1 v2 v3 v4 v5 v6 v7 -> coe v7
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.ProtocolL.Vote
d_Vote_102 = ()
data T_Vote_102 = C_MkVote_116 Integer AgdaAny T_Block_70

-- Peras.ProtocolL.Vote.round_number
d_round_number_110 :: T_Vote_102 -> Integer
d_round_number_110 v0 =
  case coe v0 of
    C_MkVote_116 v1 v2 v3 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.ProtocolL.Vote.creator_ID
d_creator_ID_112 :: T_Vote_102 -> AgdaAny
d_creator_ID_112 v0 =
  case coe v0 of
    C_MkVote_116 v1 v2 v3 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.ProtocolL.Vote.block_voted_for
d_block_voted_for_114 :: T_Vote_102 -> T_Block_70
d_block_voted_for_114 v0 =
  case coe v0 of
    C_MkVote_116 v1 v2 v3 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.ProtocolL.Certify
d_Certify_118 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL.Certify"

-- Peras.ProtocolL.Chain
d_Chain_120 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL.Chain"

-- Peras.ProtocolL.null
d_null_122 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL.null"

-- Peras.ProtocolL._isLeaderInSlot_
d__isLeaderInSlot__124 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL._isLeaderInSlot_"

-- Peras.ProtocolL._trimmedBy_
d__trimmedBy__126 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL._trimmedBy_"

-- Peras.ProtocolL._isCommitteeMemberInRound_
d__isCommitteeMemberInRound__128 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL._isCommitteeMemberInRound_"

-- Peras.ProtocolL._pointsInto_
d__pointsInto__130 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL._pointsInto_"

-- Peras.ProtocolL.length
d_length_132 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL.length"

-- Peras.ProtocolL.round
d_round_134 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL.round"

-- Peras.ProtocolL.chainWeight
d_chainWeight_136 :: AgdaAny -> [AgdaAny] -> Integer
d_chainWeight_136 v0 v1 =
  coe
    MAlonzo.Code.Data.List.Base.du_foldr_242
    ( coe
        ( \v2 v3 ->
            coe
              MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
              (coe d__pointsInto__130 v2 v0)
              (coe addInt (coe d_B_42) (coe v3))
              (coe v3)
        )
    )
    (coe d_length_132 v0)
    (coe v1)

-- Peras.ProtocolL._⟦_⟧
d__'10214'_'10215'_146 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL._\10214_\10215"

-- Peras.ProtocolL.Cpref
d_Cpref_148 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL.Cpref"

-- Peras.ProtocolL.certseen
d_certseen_150 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL.certseen"

-- Peras.ProtocolL.certchain
d_certchain_152 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL.certchain"

-- Peras.ProtocolL.Vpref
d_Vpref_154 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL.Vpref"

-- Peras.ProtocolL.Certs
d_Certs_156 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.ProtocolL.Certs"

-- Peras.ProtocolL.Node
d_Node_158 a0 = ()
data T_Node_158
  = C_bind_164 T_Node_158 (AgdaAny -> T_Node_158)
  | C_ret_168 AgdaAny
  | C_forgeBlock_170 AgdaAny
  | C_latestCertificateOnChain_172 AgdaAny
  | C_latestCertificateSeen_174
  | C_mkCertificate_176 Integer T_Block_70
  | C_existsBlockWithQuorum_178
      AgdaAny
      (Maybe T_Block_70 -> T_Node_158)
  | C__extendWith__180 AgdaAny T_Block_70
  | C_output_182 AgdaAny
  | C__'58''61'__186 AgdaAny T_Node_158
  | C__'43''61'__190 AgdaAny AgdaAny

-- Peras.ProtocolL.Monad
d_Monad_194 a0 = ()
data T_Monad_194
  = C_Monad'46'constructor_821
      ( () ->
        () ->
        AgdaAny ->
        (AgdaAny -> AgdaAny) ->
        AgdaAny
      )
      (() -> AgdaAny -> AgdaAny)

-- Peras.ProtocolL.Monad._>>=_
d__'62''62''61'__212 ::
  T_Monad_194 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
d__'62''62''61'__212 v0 =
  case coe v0 of
    C_Monad'46'constructor_821 v1 v2 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.ProtocolL.Monad.return
d_return_216 :: T_Monad_194 -> () -> AgdaAny -> AgdaAny
d_return_216 v0 =
  case coe v0 of
    C_Monad'46'constructor_821 v1 v2 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.ProtocolL.Monad._>>_
d__'62''62'__222 ::
  (() -> ()) ->
  T_Monad_194 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d__'62''62'__222 ~v0 v1 ~v2 ~v3 v4 v5 = du__'62''62'__222 v1 v4 v5
du__'62''62'__222 :: T_Monad_194 -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__222 v0 v1 v2 =
  coe d__'62''62''61'__212 v0 erased erased v1 (\v3 -> v2)

-- Peras.ProtocolL.Monad.when
d_when_232 ::
  (() -> ()) -> T_Monad_194 -> () -> Bool -> AgdaAny -> AgdaAny
d_when_232 ~v0 v1 ~v2 v3 v4 = du_when_232 v1 v3 v4
du_when_232 :: T_Monad_194 -> Bool -> AgdaAny -> AgdaAny
du_when_232 v0 v1 v2 =
  coe
    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
    (coe v1)
    ( coe
        du__'62''62'__222
        (coe v0)
        (coe v2)
        ( coe
            d_return_216
            v0
            erased
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
        )
    )
    ( coe
        d_return_216
        v0
        erased
        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
    )

-- Peras.ProtocolL.NodeMonad
d_NodeMonad_238 :: T_Monad_194
d_NodeMonad_238 =
  coe
    C_Monad'46'constructor_821
    (\v0 v1 v2 v3 -> coe C_bind_164 v2 v3)
    (\v0 v1 -> coe C_ret_168 v1)

-- Peras.ProtocolL._._>>_
d__'62''62'__242 ::
  (() -> ()) ->
  T_Monad_194 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d__'62''62'__242 ~v0 v1 = du__'62''62'__242 v1
du__'62''62'__242 ::
  T_Monad_194 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__242 v0 v1 v2 v3 v4 =
  coe du__'62''62'__222 (coe v0) v3 v4

-- Peras.ProtocolL._._>>=_
d__'62''62''61'__244 ::
  T_Monad_194 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny
d__'62''62''61'__244 v0 = coe d__'62''62''61'__212 (coe v0)

-- Peras.ProtocolL._.return
d_return_246 :: T_Monad_194 -> () -> AgdaAny -> AgdaAny
d_return_246 v0 = coe d_return_216 (coe v0)

-- Peras.ProtocolL._.when
d_when_248 ::
  (() -> ()) -> T_Monad_194 -> () -> Bool -> AgdaAny -> AgdaAny
d_when_248 ~v0 v1 = du_when_248 v1
du_when_248 :: T_Monad_194 -> () -> Bool -> AgdaAny -> AgdaAny
du_when_248 v0 v1 v2 v3 = coe du_when_232 (coe v0) v2 v3

-- Peras.ProtocolL.onNewSlot
d_onNewSlot_250 :: AgdaAny -> Integer -> T_Node_158
d_onNewSlot_250 v0 v1 =
  coe
    du_when_232
    (coe d_NodeMonad_238)
    (coe d__isLeaderInSlot__124 v0 v1)
    ( coe
        d__'62''62''61'__212
        d_NodeMonad_238
        erased
        erased
        (coe C_forgeBlock_170 (coe d_Cpref_148))
        ( \v2 ->
            coe
              du_when_232
              (coe d_NodeMonad_238)
              ( coe
                  MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                  ( coe
                      d__'61''61'__10
                      erased
                      ( coe
                          d__'91'_'93'_6
                          erased
                          d_Certs_156
                          (coe d__'45'__20 (coe d__'47'__22 v1 d_U_34) (2 :: Integer))
                      )
                      d_null_122
                  )
                  ( coe
                      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                      ( coe
                          d__'8804'__14
                          ( coe
                              d__'45'__20
                              (coe d__'47'__22 v1 d_U_34)
                              (coe d_round_134 d_certseen_150)
                          )
                          d_A_36
                      )
                      ( coe
                          d__'62'__18
                          (coe d_round_134 d_certseen_150)
                          (coe d_round_134 d_certchain_152)
                      )
                  )
              )
              ( coe
                  d__'62''62''61'__212
                  d_NodeMonad_238
                  erased
                  erased
                  ( coe
                      C__extendWith__180
                      (coe d_Cpref_148)
                      (coe d_Certify_118 v2 d_certseen_150)
                  )
                  (\v3 -> coe C_output_182 (coe d__trimmedBy__126 v3 d_W_38))
              )
        )
    )

-- Peras.ProtocolL.voteInRound
d_voteInRound_264 :: AgdaAny -> [AgdaAny] -> Integer -> Bool
d_voteInRound_264 ~v0 ~v1 v2 = du_voteInRound_264 v2
du_voteInRound_264 :: Integer -> Bool
du_voteInRound_264 v0 =
  coe
    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
    ( coe
        MAlonzo.Code.Data.Bool.Base.d__'8743'__24
        ( coe
            d__'61''61'__10
            erased
            (coe d_round_134 d_certseen_150)
            (coe d__'45'__20 v0 (1 :: Integer))
        )
        (coe d__pointsInto__130 d_certseen_150 d_Cpref_148)
    )
    ( coe
        MAlonzo.Code.Data.Bool.Base.d__'8743'__24
        ( coe
            d__'8805'__16
            (coe d__'45'__20 v0 (coe d_round_134 d_certseen_150))
            d_R_46
        )
        ( coe
            du_cooldownHasPassed_276
            (coe d__'45'__20 v0 (coe d_round_134 d_certchain_152))
        )
    )

-- Peras.ProtocolL._.cooldownHasPassed
d_cooldownHasPassed_276 ::
  AgdaAny -> [AgdaAny] -> Integer -> Integer -> Bool
d_cooldownHasPassed_276 ~v0 ~v1 ~v2 v3 =
  du_cooldownHasPassed_276 v3
du_cooldownHasPassed_276 :: Integer -> Bool
du_cooldownHasPassed_276 v0 =
  let v1 = d_K_48
   in coe
        ( case coe v1 of
            0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
            _ ->
              let v2 = subInt (coe d_K_48) (coe (1 :: Integer))
               in coe
                    ( coe
                        MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                        (coe d__'62'__18 (coe du_q_294 v2 v0 erased) (0 :: Integer))
                        ( coe
                            d__'61''61'__10
                            erased
                            (coe du_r''_296 v2 v0 erased)
                            (0 :: Integer)
                        )
                    )
        )

-- Peras.ProtocolL._._.q
d_q_294 ::
  Integer ->
  AgdaAny ->
  [AgdaAny] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  Integer
d_q_294 v0 ~v1 ~v2 ~v3 v4 = du_q_294 v0 v4
du_q_294 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  Integer
du_q_294 v0 v1 =
  coe
    MAlonzo.Code.Data.Nat.DivMod.d__div__1096
    v1
    (addInt (coe (1 :: Integer)) (coe v0))

-- Peras.ProtocolL._._.r'
d_r''_296 ::
  Integer ->
  AgdaAny ->
  [AgdaAny] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  Integer
d_r''_296 v0 ~v1 ~v2 ~v3 v4 = du_r''_296 v0 v4
du_r''_296 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  Integer
du_r''_296 v0 v1 v2 =
  coe
    MAlonzo.Code.Data.Nat.Base.du__'37'__326
    (coe v1)
    (coe addInt (coe (1 :: Integer)) (coe v0))

-- Peras.ProtocolL.onNewRound
d_onNewRound_298 :: AgdaAny -> Integer -> T_Node_158
d_onNewRound_298 v0 v1 =
  coe
    du_when_232
    (coe d_NodeMonad_238)
    ( coe
        MAlonzo.Code.Data.Bool.Base.d__'8743'__24
        (coe d__isCommitteeMemberInRound__128 v0 v1)
        (coe du_voteInRound_264 (coe v1))
    )
    ( coe
        C__'43''61'__190
        (coe d__'91'_'93'_6 erased d_Vpref_154 v1)
        ( coe
            d_singleton_28
            erased
            ( coe
                C_MkVote_116
                (coe v1)
                (coe v0)
                ( coe
                    d__'10214'_'10215'_146
                    d_Cpref_148
                    (coe d__'45'__20 (d_slot_54 (coe v1)) d_L_40)
                )
            )
        )
    )

-- Peras.ProtocolL.onPeerVotesChange
d_onPeerVotesChange_304 :: AgdaAny -> Integer -> T_Node_158
d_onPeerVotesChange_304 v0 v1 =
  coe
    du_when_232
    (coe d_NodeMonad_238)
    ( coe
        d__'61''61'__10
        erased
        (coe d__'91'_'93'_6 erased d_Certs_156 v1)
        d_null_122
    )
    ( coe
        du__'62''62'__222
        (coe d_NodeMonad_238)
        ( coe
            C__'43''61'__190
            (coe d__'91'_'93'_6 erased d_Vpref_154 v1)
            v0
        )
        ( coe
            C_existsBlockWithQuorum_178
            (coe d__'91'_'93'_6 erased d_Vpref_154 v1)
            ( coe
                ( \v2 ->
                    case coe v2 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3 ->
                        coe
                          C__'58''61'__186
                          (coe d__'91'_'93'_6 erased d_Certs_156 v1)
                          (coe C_mkCertificate_176 (coe v1) (coe v3))
                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 ->
                        coe
                          d_return_216
                          d_NodeMonad_238
                          erased
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      _ -> MAlonzo.RTE.mazUnreachableError
                )
            )
        )
    )

-- Peras.ProtocolL.onPeerCertsChange
d_onPeerCertsChange_314 :: AgdaAny -> Integer -> T_Node_158
d_onPeerCertsChange_314 v0 v1 =
  coe
    du_when_232
    (coe d_NodeMonad_238)
    ( coe
        d__'61''61'__10
        erased
        (coe d__'91'_'93'_6 erased d_Certs_156 v1)
        d_null_122
    )
    ( coe
        C__'58''61'__186
        (coe d__'91'_'93'_6 erased d_Certs_156 v1)
        (coe d_return_216 d_NodeMonad_238 erased v0)
    )

-- Peras.ProtocolL.onPeerChainChange
d_onPeerChainChange_320 :: AgdaAny -> AgdaAny -> T_Node_158
d_onPeerChainChange_320 v0 ~v1 = du_onPeerChainChange_320 v0
du_onPeerChainChange_320 :: AgdaAny -> T_Node_158
du_onPeerChainChange_320 v0 =
  coe
    du__'62''62'__222
    (coe d_NodeMonad_238)
    ( coe
        du_when_232
        (coe d_NodeMonad_238)
        ( coe
            d__'62'__18
            (d_chainWeight_136 (coe v0) (coe d_Certs_156))
            (d_chainWeight_136 (coe d_Cpref_148) (coe d_Certs_156))
        )
        ( coe
            C__'58''61'__186
            d_Cpref_148
            (coe d_return_216 d_NodeMonad_238 erased v0)
        )
    )
    (coe C_output_182 (coe d__trimmedBy__126 d_Cpref_148 d_W_38))
