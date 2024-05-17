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

module MAlonzo.Code.Peras.QQCD.Types where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Haskell.Prim
import qualified MAlonzo.Code.Haskell.Prim.Maybe
import qualified MAlonzo.Code.Peras.QQCD.Crypto
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

import qualified Data.ByteString as BS

-- Peras.QCD.Types.MembershipProof
d_MembershipProof_6 = ()
newtype T_MembershipProof_6
  = C_MakeMembershipProof_12 MAlonzo.Code.Peras.QQCD.Crypto.T_ByteString_6

-- Peras.QCD.Types.MembershipProof.membershipProofBytes
d_membershipProofBytes_10 ::
  T_MembershipProof_6 ->
  MAlonzo.Code.Peras.QQCD.Crypto.T_ByteString_6
d_membershipProofBytes_10 v0 =
  case coe v0 of
    C_MakeMembershipProof_12 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Types.LeadershipProof
d_LeadershipProof_14 = ()
newtype T_LeadershipProof_14
  = C_MakeLeadershipProof_20 MAlonzo.Code.Peras.QQCD.Crypto.T_ByteString_6

-- Peras.QCD.Types.LeadershipProof.leadershipProofBytes
d_leadershipProofBytes_18 ::
  T_LeadershipProof_14 ->
  MAlonzo.Code.Peras.QQCD.Crypto.T_ByteString_6
d_leadershipProofBytes_18 v0 =
  case coe v0 of
    C_MakeLeadershipProof_20 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Types.Signature
d_Signature_22 = ()
newtype T_Signature_22
  = C_MakeSignature_28 MAlonzo.Code.Peras.QQCD.Crypto.T_ByteString_6

-- Peras.QCD.Types.Signature.signatureBytes
d_signatureBytes_26 ::
  T_Signature_22 -> MAlonzo.Code.Peras.QQCD.Crypto.T_ByteString_6
d_signatureBytes_26 v0 =
  case coe v0 of
    C_MakeSignature_28 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Types.VerificationKey
d_VerificationKey_30 = ()
newtype T_VerificationKey_30
  = C_MakeVerificationKey_36 MAlonzo.Code.Peras.QQCD.Crypto.T_ByteString_6

-- Peras.QCD.Types.VerificationKey.verificationKeyBytes
d_verificationKeyBytes_34 ::
  T_VerificationKey_30 ->
  MAlonzo.Code.Peras.QQCD.Crypto.T_ByteString_6
d_verificationKeyBytes_34 v0 =
  case coe v0 of
    C_MakeVerificationKey_36 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Types.Slot
d_Slot_38 :: ()
d_Slot_38 = erased

-- Peras.QCD.Types.Round
d_Round_40 :: ()
d_Round_40 = erased

-- Peras.QCD.Types.PartyId
d_PartyId_42 :: ()
d_PartyId_42 = erased

-- Peras.QCD.Types.Weight
d_Weight_44 :: ()
d_Weight_44 = erased

-- Peras.QCD.Types.Certificate
d_Certificate_46 = ()
data T_Certificate_46
  = C_MakeCertificate_110
      Integer
      MAlonzo.Code.Peras.QQCD.Crypto.T_Hash_16
      MAlonzo.Code.Peras.QQCD.Crypto.T_ByteString_6

-- Peras.QCD.Types.Tx
d_Tx_48 :: ()
d_Tx_48 = erased

-- Peras.QCD.Types.Block
d_Block_50 = ()
data T_Block_50
  = C_MakeBlock_80
      Integer
      T_VerificationKey_30
      MAlonzo.Code.Peras.QQCD.Crypto.T_Hash_16
      MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10
      T_LeadershipProof_14
      T_Signature_22
      MAlonzo.Code.Peras.QQCD.Crypto.T_Hash_16

-- Peras.QCD.Types.Block.slot
d_slot_66 :: T_Block_50 -> Integer
d_slot_66 v0 =
  case coe v0 of
    C_MakeBlock_80 v1 v2 v3 v4 v5 v6 v7 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Types.Block.creator
d_creator_68 :: T_Block_50 -> T_VerificationKey_30
d_creator_68 v0 =
  case coe v0 of
    C_MakeBlock_80 v1 v2 v3 v4 v5 v6 v7 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Types.Block.parent
d_parent_70 ::
  T_Block_50 -> MAlonzo.Code.Peras.QQCD.Crypto.T_Hash_16
d_parent_70 v0 =
  case coe v0 of
    C_MakeBlock_80 v1 v2 v3 v4 v5 v6 v7 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Types.Block.certificate
d_certificate_72 ::
  T_Block_50 -> MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10
d_certificate_72 v0 =
  case coe v0 of
    C_MakeBlock_80 v1 v2 v3 v4 v5 v6 v7 -> coe v4
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Types.Block.leadershipProof
d_leadershipProof_74 :: T_Block_50 -> T_LeadershipProof_14
d_leadershipProof_74 v0 =
  case coe v0 of
    C_MakeBlock_80 v1 v2 v3 v4 v5 v6 v7 -> coe v5
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Types.Block.signature
d_signature_76 :: T_Block_50 -> T_Signature_22
d_signature_76 v0 =
  case coe v0 of
    C_MakeBlock_80 v1 v2 v3 v4 v5 v6 v7 -> coe v6
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Types.Block.bodyHash
d_bodyHash_78 ::
  T_Block_50 -> MAlonzo.Code.Peras.QQCD.Crypto.T_Hash_16
d_bodyHash_78 v0 =
  case coe v0 of
    C_MakeBlock_80 v1 v2 v3 v4 v5 v6 v7 -> coe v7
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Types.BlockBody
d_BlockBody_82 = ()
data T_BlockBody_82
  = C_MakeBlockBody_92
      MAlonzo.Code.Peras.QQCD.Crypto.T_Hash_16
      [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]

-- Peras.QCD.Types.BlockBody.headerHash
d_headerHash_88 ::
  T_BlockBody_82 -> MAlonzo.Code.Peras.QQCD.Crypto.T_Hash_16
d_headerHash_88 v0 =
  case coe v0 of
    C_MakeBlockBody_92 v1 v2 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Types.BlockBody.payload
d_payload_90 ::
  T_BlockBody_82 -> [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
d_payload_90 v0 =
  case coe v0 of
    C_MakeBlockBody_92 v1 v2 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Types.Chain
d_Chain_94 :: ()
d_Chain_94 = erased

-- Peras.QCD.Types.genesisHash
d_genesisHash_96 :: MAlonzo.Code.Peras.QQCD.Crypto.T_Hash_16
d_genesisHash_96 =
  coe
    MAlonzo.Code.Peras.QQCD.Crypto.C_MakeHash_24
    (coe MAlonzo.Code.Peras.QQCD.Crypto.d_emptyBS_8)

-- Peras.QCD.Types.Certificate.certificateRound
d_certificateRound_104 :: T_Certificate_46 -> Integer
d_certificateRound_104 v0 =
  case coe v0 of
    C_MakeCertificate_110 v1 v2 v3 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Types.Certificate.certificateBlock
d_certificateBlock_106 ::
  T_Certificate_46 -> MAlonzo.Code.Peras.QQCD.Crypto.T_Hash_16
d_certificateBlock_106 v0 =
  case coe v0 of
    C_MakeCertificate_110 v1 v2 v3 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Types.Certificate.certificateBytes
d_certificateBytes_108 ::
  T_Certificate_46 -> MAlonzo.Code.Peras.QQCD.Crypto.T_ByteString_6
d_certificateBytes_108 v0 =
  case coe v0 of
    C_MakeCertificate_110 v1 v2 v3 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Types.genesisCert
d_genesisCert_112 :: T_Certificate_46
d_genesisCert_112 =
  coe
    C_MakeCertificate_110
    (coe (0 :: Integer))
    (coe d_genesisHash_96)
    (coe MAlonzo.Code.Peras.QQCD.Crypto.d_emptyBS_8)

-- Peras.QCD.Types.certsOnChain
d_certsOnChain_114 :: [T_Block_50] -> [T_Certificate_46]
d_certsOnChain_114 v0 =
  case coe v0 of
    [] ->
      coe
        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
        (coe d_genesisCert_112)
        (coe v0)
    (:) v1 v2 ->
      coe
        MAlonzo.Code.Haskell.Prim.du__'36'__48
        ( coe
            MAlonzo.Code.Haskell.Prim.Maybe.du_maybe_28
            (coe (\v3 -> v3))
            (coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22)
            (coe d_certificate_72 (coe v1))
        )
        (coe d_certsOnChain_114 (coe v2))
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Types.lastCert
d_lastCert_120 :: [T_Block_50] -> T_Certificate_46
d_lastCert_120 v0 =
  case coe v0 of
    [] -> coe d_genesisCert_112
    (:) v1 v2 ->
      coe
        MAlonzo.Code.Haskell.Prim.Maybe.du_maybe_28
        (coe d_lastCert_120 (coe v2))
        (coe (\v3 -> v3))
        (coe d_certificate_72 (coe v1))
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Types.Vote
d_Vote_126 = ()
data T_Vote_126
  = C_MakeVote_152
      Integer
      T_VerificationKey_30
      Integer
      MAlonzo.Code.Peras.QQCD.Crypto.T_Hash_16
      T_MembershipProof_6
      T_Signature_22

-- Peras.QCD.Types.Vote.voteRound
d_voteRound_140 :: T_Vote_126 -> Integer
d_voteRound_140 v0 =
  case coe v0 of
    C_MakeVote_152 v1 v2 v3 v4 v5 v6 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Types.Vote.voteParty
d_voteParty_142 :: T_Vote_126 -> T_VerificationKey_30
d_voteParty_142 v0 =
  case coe v0 of
    C_MakeVote_152 v1 v2 v3 v4 v5 v6 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Types.Vote.voteWeight
d_voteWeight_144 :: T_Vote_126 -> Integer
d_voteWeight_144 v0 =
  case coe v0 of
    C_MakeVote_152 v1 v2 v3 v4 v5 v6 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Types.Vote.voteBlock
d_voteBlock_146 ::
  T_Vote_126 -> MAlonzo.Code.Peras.QQCD.Crypto.T_Hash_16
d_voteBlock_146 v0 =
  case coe v0 of
    C_MakeVote_152 v1 v2 v3 v4 v5 v6 -> coe v4
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Types.Vote.voteProof
d_voteProof_148 :: T_Vote_126 -> T_MembershipProof_6
d_voteProof_148 v0 =
  case coe v0 of
    C_MakeVote_152 v1 v2 v3 v4 v5 v6 -> coe v5
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Types.Vote.voteSignature
d_voteSignature_150 :: T_Vote_126 -> T_Signature_22
d_voteSignature_150 v0 =
  case coe v0 of
    C_MakeVote_152 v1 v2 v3 v4 v5 v6 -> coe v6
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Types.Message
d_Message_154 = ()
data T_Message_154
  = C_NewChain_156 [T_Block_50]
  | C_NewVote_158 T_Vote_126
