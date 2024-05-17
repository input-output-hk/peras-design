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

module MAlonzo.Code.Peras.Message where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Peras.Block
import qualified MAlonzo.Code.Peras.Chain
import qualified MAlonzo.Code.Peras.Crypto
import qualified MAlonzo.Code.Peras.Numbering
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

-- Peras.Message.NodeId
d_NodeId_4 = ()
newtype T_NodeId_4
  = C_MkNodeId_10 MAlonzo.Code.Agda.Builtin.String.T_String_6

-- Peras.Message.NodeId.nodeId
d_nodeId_8 ::
  T_NodeId_4 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_nodeId_8 v0 =
  case coe v0 of
    C_MkNodeId_10 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Message.Message
d_Message_12 = ()
data T_Message_12
  = C_NextSlot_14 MAlonzo.Code.Peras.Numbering.T_SlotNumber_4
  | C_NewChain_16 [MAlonzo.Code.Peras.Block.T_Block_62]
  | C_SomeVote_18 MAlonzo.Code.Peras.Chain.T_Vote_4
  | C_SomeCertificate_20 MAlonzo.Code.Peras.Block.T_Certificate_66
  | C_FetchVotes_22
      [ MAlonzo.Code.Peras.Crypto.T_Hash_14
          MAlonzo.Code.Peras.Chain.T_Vote_4
      ]
  | C_FollowChain_24
      ( MAlonzo.Code.Peras.Crypto.T_Hash_14
          [MAlonzo.Code.Peras.Block.T_Block_62]
      )
  | C_RollForward_26 MAlonzo.Code.Peras.Block.T_Block_62
  | C_RollBack_28 MAlonzo.Code.Peras.Block.T_Block_62
  | C_FetchBlocks_30
      [ MAlonzo.Code.Peras.Crypto.T_Hash_14
          MAlonzo.Code.Peras.Block.T_Block_62
      ]
  | C_SomeBlock_32 MAlonzo.Code.Peras.Block.T_BlockBody_64
