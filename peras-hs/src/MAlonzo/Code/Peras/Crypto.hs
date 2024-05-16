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

module MAlonzo.Code.Peras.Crypto where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Haskell.Prim.Eq
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
import qualified Peras.Crypto as G

-- Peras.Crypto.ByteString
type T_ByteString_4 = BS.ByteString
d_ByteString_4 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Crypto.ByteString"

-- Peras.Crypto.emptyBS
d_emptyBS_6 :: T_ByteString_4
d_emptyBS_6 = BS.empty

-- Peras.Crypto.eqBS
d_eqBS_8 :: T_ByteString_4 -> T_ByteString_4 -> Bool
d_eqBS_8 = (==)

-- Peras.Crypto._isInfixOf_
d__isInfixOf__10 :: T_ByteString_4 -> T_ByteString_4 -> Bool
d__isInfixOf__10 = BS.isInfixOf

-- Peras.Crypto.Hash
d_Hash_14 a0 = ()
type T_Hash_14 a0 = G.Hash a0
pattern C_MkHash_22 a0 = G.MkHash a0
check_MkHash_22 :: forall xa. T_ByteString_4 -> T_Hash_14 xa
check_MkHash_22 = G.MkHash
cover_Hash_14 :: G.Hash a1 -> ()
cover_Hash_14 x =
  case x of
    G.MkHash _ -> ()

-- Peras.Crypto.Hash.hashBytes
d_hashBytes_20 :: T_Hash_14 AgdaAny -> T_ByteString_4
d_hashBytes_20 v0 =
  case coe v0 of
    C_MkHash_22 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Crypto.iHashEq
d_iHashEq_26 :: () -> MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8
d_iHashEq_26 ~v0 = du_iHashEq_26
du_iHashEq_26 :: MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8
du_iHashEq_26 =
  coe
    MAlonzo.Code.Haskell.Prim.Eq.C_Eq'46'constructor_7
    ( coe
        ( \v0 v1 ->
            coe d_eqBS_8 (d_hashBytes_20 (coe v0)) (d_hashBytes_20 (coe v1))
        )
    )

-- Peras.Crypto.Hashable
d_Hashable_34 a0 = ()
newtype T_Hashable_34
  = C_Hashable'46'constructor_173 (AgdaAny -> T_Hash_14 AgdaAny)

-- Peras.Crypto.Hashable.hash
d_hash_40 :: T_Hashable_34 -> AgdaAny -> T_Hash_14 AgdaAny
d_hash_40 v0 =
  case coe v0 of
    C_Hashable'46'constructor_173 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Crypto.MembershipProof
d_MembershipProof_42 = ()
type T_MembershipProof_42 = G.MembershipProof
pattern C_MkMembershipProof_48 a0 = G.MkMembershipProof a0
check_MkMembershipProof_48 ::
  T_ByteString_4 -> T_MembershipProof_42
check_MkMembershipProof_48 = G.MkMembershipProof
cover_MembershipProof_42 :: G.MembershipProof -> ()
cover_MembershipProof_42 x =
  case x of
    G.MkMembershipProof _ -> ()

-- Peras.Crypto.MembershipProof.proofM
d_proofM_46 :: T_MembershipProof_42 -> T_ByteString_4
d_proofM_46 v0 =
  case coe v0 of
    C_MkMembershipProof_48 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Crypto.iMembershipProofEq
d_iMembershipProofEq_50 :: MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8
d_iMembershipProofEq_50 =
  coe
    MAlonzo.Code.Haskell.Prim.Eq.C_Eq'46'constructor_7
    ( coe
        ( \v0 v1 ->
            coe d_eqBS_8 (d_proofM_46 (coe v0)) (d_proofM_46 (coe v1))
        )
    )

-- Peras.Crypto.LeadershipProof
d_LeadershipProof_56 = ()
type T_LeadershipProof_56 = G.LeadershipProof
pattern C_MkLeadershipProof_62 a0 = G.MkLeadershipProof a0
check_MkLeadershipProof_62 ::
  T_ByteString_4 -> T_LeadershipProof_56
check_MkLeadershipProof_62 = G.MkLeadershipProof
cover_LeadershipProof_56 :: G.LeadershipProof -> ()
cover_LeadershipProof_56 x =
  case x of
    G.MkLeadershipProof _ -> ()

-- Peras.Crypto.LeadershipProof.proofL
d_proofL_60 :: T_LeadershipProof_56 -> T_ByteString_4
d_proofL_60 v0 =
  case coe v0 of
    C_MkLeadershipProof_62 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Crypto.iLeadershipProofEq
d_iLeadershipProofEq_64 :: MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8
d_iLeadershipProofEq_64 =
  coe
    MAlonzo.Code.Haskell.Prim.Eq.C_Eq'46'constructor_7
    ( coe
        ( \v0 v1 ->
            coe d_eqBS_8 (d_proofL_60 (coe v0)) (d_proofL_60 (coe v1))
        )
    )

-- Peras.Crypto.Signature
d_Signature_70 = ()
type T_Signature_70 = G.Signature
pattern C_MkSignature_76 a0 = G.MkSignature a0
check_MkSignature_76 :: T_ByteString_4 -> T_Signature_70
check_MkSignature_76 = G.MkSignature
cover_Signature_70 :: G.Signature -> ()
cover_Signature_70 x =
  case x of
    G.MkSignature _ -> ()

-- Peras.Crypto.Signature.bytesS
d_bytesS_74 :: T_Signature_70 -> T_ByteString_4
d_bytesS_74 v0 =
  case coe v0 of
    C_MkSignature_76 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Crypto.iSignatureEq
d_iSignatureEq_78 :: MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8
d_iSignatureEq_78 =
  coe
    MAlonzo.Code.Haskell.Prim.Eq.C_Eq'46'constructor_7
    ( coe
        ( \v0 v1 ->
            coe d_eqBS_8 (d_bytesS_74 (coe v0)) (d_bytesS_74 (coe v1))
        )
    )

-- Peras.Crypto.VerificationKey
d_VerificationKey_84 = ()
type T_VerificationKey_84 = G.VerificationKey
pattern C_MkVerificationKey_90 a0 = G.MkVerificationKey a0
check_MkVerificationKey_90 ::
  T_ByteString_4 -> T_VerificationKey_84
check_MkVerificationKey_90 = G.MkVerificationKey
cover_VerificationKey_84 :: G.VerificationKey -> ()
cover_VerificationKey_84 x =
  case x of
    G.MkVerificationKey _ -> ()

-- Peras.Crypto.VerificationKey.keyV
d_keyV_88 :: T_VerificationKey_84 -> T_ByteString_4
d_keyV_88 v0 =
  case coe v0 of
    C_MkVerificationKey_90 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Crypto.iVerificationKeyEq
d_iVerificationKeyEq_92 :: MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8
d_iVerificationKeyEq_92 =
  coe
    MAlonzo.Code.Haskell.Prim.Eq.C_Eq'46'constructor_7
    ( coe
        ( \v0 v1 ->
            coe d_eqBS_8 (d_keyV_88 (coe v0)) (d_keyV_88 (coe v1))
        )
    )

-- Peras.Crypto.isCommitteeMember
d_isCommitteeMember_98 ::
  T_VerificationKey_84 -> T_MembershipProof_42 -> Bool
d_isCommitteeMember_98 v0 v1 =
  case coe v0 of
    C_MkVerificationKey_90 v2 ->
      case coe v1 of
        C_MkMembershipProof_48 v3 -> coe d__isInfixOf__10 v2 v3
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Crypto.verify
d_verify_104 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Crypto.verify"
