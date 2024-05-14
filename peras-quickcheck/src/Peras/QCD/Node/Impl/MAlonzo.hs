{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}

module Peras.QCD.Node.Impl.MAlonzo (
  MAlonzoNode,
) where

import Data.Default (Default (..))
import Peras.QCD.Node.API (PerasNode (..))
import Prelude hiding (round)

import qualified MAlonzo.Code.Haskell.Prim.Maybe as M.Maybe
import qualified MAlonzo.Code.Haskell.Prim.Tuple as M.Tuple
import qualified MAlonzo.Code.Peras.QQCD.Crypto as M
import qualified MAlonzo.Code.Peras.QQCD.Node.Model as M
import qualified MAlonzo.Code.Peras.QQCD.Node.Specification as M
import qualified MAlonzo.Code.Peras.QQCD.Protocol as M
import qualified MAlonzo.Code.Peras.QQCD.State as M
import qualified MAlonzo.Code.Peras.QQCD.Types as M
import qualified MAlonzo.RTE as M (AgdaAny, coe)

import qualified Peras.QCD.Crypto as S
import qualified Peras.QCD.Node.Model as S
import qualified Peras.QCD.Protocol as S
import qualified Peras.QCD.Types as S

type MAlonzoNode = M.T_NodeModel_8

toParams :: M.T_Params_26 -> S.Params
toParams (M.C_Params'46'constructor_233 u a w l b t r k) =
  S.Params
    (fromIntegral u)
    (fromIntegral a)
    (fromIntegral w)
    (fromIntegral l)
    (fromIntegral b)
    (fromIntegral t)
    (fromIntegral r)
    (fromIntegral k)

fromParams :: S.Params -> M.T_Params_26
fromParams (S.Params u a w l b t r k) =
  M.C_Params'46'constructor_233
    (toInteger u)
    (toInteger a)
    (toInteger w)
    (toInteger l)
    (toInteger b)
    (toInteger t)
    (toInteger r)
    (toInteger k)

toMembershipProof :: M.T_MembershipProof_6 -> S.MembershipProof
toMembershipProof (M.C_MakeMembershipProof_12 x) = S.MakeMembershipProof x

fromMembershipProof :: S.MembershipProof -> M.T_MembershipProof_6
fromMembershipProof (S.MakeMembershipProof x) = M.C_MakeMembershipProof_12 x

toLeadershipProof :: M.T_LeadershipProof_14 -> S.LeadershipProof
toLeadershipProof (M.C_MakeLeadershipProof_20 x) = S.MakeLeadershipProof x

fromLeadershipProof :: S.LeadershipProof -> M.T_LeadershipProof_14
fromLeadershipProof (S.MakeLeadershipProof x) = M.C_MakeLeadershipProof_20 x

toSignature :: M.T_Signature_22 -> S.Signature
toSignature (M.C_MakeSignature_28 x) = S.MakeSignature x

fromSignature :: S.Signature -> M.T_Signature_22
fromSignature (S.MakeSignature x) = M.C_MakeSignature_28 x

toVerificationKey :: M.T_VerificationKey_30 -> S.VerificationKey
toVerificationKey (M.C_MakeVerificationKey_36 x) = S.MakeVerificationKey x

fromVerificationKey :: S.VerificationKey -> M.T_VerificationKey_30
fromVerificationKey (S.MakeVerificationKey x) = M.C_MakeVerificationKey_36 x

toCert :: M.T_Certificate_46 -> S.Certificate
toCert (M.C_MakeCertificate_110 round block bytes) =
  S.MakeCertificate
    (fromIntegral round)
    (toHash block)
    bytes

fromCert :: S.Certificate -> M.T_Certificate_46
fromCert (S.MakeCertificate round block bytes) =
  M.C_MakeCertificate_110
    (toInteger round)
    (fromHash block)
    bytes

toBlock :: M.T_Block_50 -> S.Block
toBlock (M.C_MakeBlock_80 slot creator parent certificate leadershipProof signature bodyHash) =
  S.MakeBlock
    (fromIntegral slot)
    (toVerificationKey creator)
    (toHash parent)
    (toMaybe certificate)
    (toLeadershipProof leadershipProof)
    (toSignature signature)
    (toHash bodyHash)

fromBlock :: S.Block -> M.T_Block_50
fromBlock (S.MakeBlock slot creator parent certificate leadershipProof signature bodyHash) =
  M.C_MakeBlock_80
    (toInteger slot)
    (fromVerificationKey creator)
    (fromHash parent)
    (fromMaybe M.coe certificate)
    (fromLeadershipProof leadershipProof)
    (fromSignature signature)
    (fromHash bodyHash)

toHash :: M.T_Hash_16 -> S.Hash a
toHash (M.C_MakeHash_24 bytes) = S.MakeHash bytes

fromHash :: S.Hash a -> M.T_Hash_16
fromHash (S.MakeHash bytes) = M.C_MakeHash_24 bytes

toMaybe :: M.Maybe.T_Maybe_10 -> Maybe a
toMaybe M.Maybe.C_Nothing_16 = Nothing
toMaybe (M.Maybe.C_Just_18 x) = Just $ M.coe x

fromMaybe :: (a -> M.AgdaAny) -> Maybe a -> M.Maybe.T_Maybe_10
fromMaybe _ Nothing = M.Maybe.C_Nothing_16
fromMaybe f (Just x) = M.Maybe.C_Just_18 $ f x

toBlockBody :: M.T_BlockBody_82 -> S.BlockBody
toBlockBody (M.C_MakeBlockBody_92 headerHash payload) =
  S.MakeBlockBody
    (toHash headerHash)
    payload

fromBlockBody :: S.BlockBody -> M.T_BlockBody_82
fromBlockBody (S.MakeBlockBody headerHash payload) =
  M.C_MakeBlockBody_92
    (fromHash headerHash)
    payload

toVote :: M.T_Vote_126 -> S.Vote
toVote (M.C_MakeVote_152 round party weight block proof signature) =
  S.MakeVote
    (fromIntegral round)
    (toVerificationKey party)
    (fromIntegral weight)
    (toHash block)
    (toMembershipProof proof)
    (toSignature signature)

fromVote :: S.Vote -> M.T_Vote_126
fromVote (S.MakeVote round party weight block proof signature) =
  M.C_MakeVote_152
    (toInteger round)
    (fromVerificationKey party)
    (toInteger weight)
    (fromHash block)
    (fromMembershipProof proof)
    (fromSignature signature)

toMessage :: M.T_Message_154 -> S.Message
toMessage (M.C_NewChain_156 chain) = S.NewChain $ toBlock <$> chain
toMessage (M.C_NewVote_158 vote) = S.NewVote $ toVote vote

fromMessage :: S.Message -> M.T_Message_154
fromMessage (S.NewChain chain) = M.C_NewChain_156 $ fromBlock <$> chain
fromMessage (S.NewVote vote) = M.C_NewVote_158 $ fromVote vote

toNodeModel :: M.T_NodeModel_8 -> S.NodeModel
toNodeModel (M.C_NodeModel'46'constructor_205 protocol creatorId currentSlot currentRound preferredChain chains votes certs latestCertSeen latestCertOnChain) =
  S.NodeModel
    (toParams protocol)
    (toVerificationKey creatorId)
    (fromIntegral currentSlot)
    (fromIntegral currentRound)
    (toBlock <$> preferredChain)
    (fmap toBlock <$> chains)
    (toVote <$> votes)
    (toCert <$> certs)
    (toCert latestCertSeen)
    (toCert latestCertOnChain)

fromNodeModel :: S.NodeModel -> M.T_NodeModel_8
fromNodeModel (S.NodeModel protocol creatorId currentSlot currentRound preferredChain chains votes certs latestCertSeen latestCertOnChain) =
  M.C_NodeModel'46'constructor_205
    (fromParams protocol)
    (fromVerificationKey creatorId)
    (toInteger currentSlot)
    (toInteger currentRound)
    (fromBlock <$> preferredChain)
    (fmap fromBlock <$> chains)
    (fromVote <$> votes)
    (fromCert <$> certs)
    (fromCert latestCertSeen)
    (fromCert latestCertOnChain)

runState' :: M.T_State_10 -> M.T_NodeModel_8 -> ([S.Message], M.T_NodeModel_8)
runState' action node =
  let
    M.Tuple.C__'44'__24 x s = M.d_runState_18 action $ M.coe node
   in
    (toMessage <$> M.coe x, M.coe s)

instance Default MAlonzoNode where
  def = M.d_emptyNode_50

instance Monad m => PerasNode MAlonzoNode m where
  initialize params party =
    pure
      . runState'
        (M.d_initialize_8 (fromParams params) (fromVerificationKey party))
  fetching chains votes =
    pure . runState' (M.d_fetching_136 (fmap fromBlock <$> chains) (fromVote <$> votes))
  blockCreation txs =
    pure . runState' (M.d_blockCreation_160 txs)
  voting weight =
    pure . runState' (M.d_voting_250 $ toInteger weight)
