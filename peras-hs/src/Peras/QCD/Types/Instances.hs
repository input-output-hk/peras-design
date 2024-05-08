{-# OPTIONS_GHC -fno-warn-orphans #-}

module Peras.QCD.Types.Instances where

import Peras.QCD.Crypto (Hash, Hashable (hash), castHash)
import Peras.QCD.Types (Block (bodyHash, certificate, creator, leadershipProof, parent, signature, slot), BlockBody (headerHash, payload), Certificate (certificateBlock, certificateBytes, certificateRound), Chain (ChainBlock, Genesis), LeadershipProof (leadershipProofBytes), MembershipProof (membershipProofBytes), Message (NewCertificate, NewChain, NewVote), Signature (signatureBytes), VerificationKey (verificationKeyBytes), Vote (voteBlock, voteParty, voteProof, voteRound, voteSignature), genesisHash)
import Peras.QCD.Util (eqBy, eqByBS)

instance Eq MembershipProof where
  (==) = eqByBS (\r -> membershipProofBytes r)

instance Hashable MembershipProof where
  hash = castHash . hash . \r -> membershipProofBytes r

instance Eq LeadershipProof where
  (==) = eqByBS (\r -> leadershipProofBytes r)

instance Hashable LeadershipProof where
  hash = castHash . hash . \r -> leadershipProofBytes r

instance Eq Signature where
  (==) = eqByBS (\r -> signatureBytes r)

instance Hashable Signature where
  hash = castHash . hash . \r -> signatureBytes r

instance Eq VerificationKey where
  (==) = eqByBS (\r -> verificationKeyBytes r)

instance Hashable VerificationKey where
  hash = castHash . hash . \r -> verificationKeyBytes r

instance Eq Vote where
  x == y =
    eqBy (\r -> voteRound r) x y
      && eqBy (\r -> voteParty r) x y
      && eqBy (\r -> voteBlock r) x y
      && eqBy (\r -> voteProof r) x y
      && eqBy (\r -> voteSignature r) x y

instance Hashable Vote where
  hash = castHash . hash . \r -> voteProof r

instance Eq Certificate where
  x == y =
    eqBy (\r -> certificateRound r) x y
      && eqBy (\r -> certificateBlock r) x y
      && eqByBS (\r -> certificateBytes r) x y

instance Hashable Certificate where
  hash x =
    castHash $
      hash (certificateRound x, certificateBlock x, certificateBytes x)

instance Eq Block where
  x == y =
    eqBy (\r -> slot r) x y
      && eqBy (\r -> creator r) x y
      && eqBy (\r -> parent r) x y
      && eqBy (\r -> certificate r) x y
      && eqBy (\r -> leadershipProof r) x y
      && eqBy (\r -> signature r) x y
      && eqBy (\r -> bodyHash r) x y

instance Hashable Block where
  hash = castHash . hash . \r -> signature r

instance Eq BlockBody where
  x == y =
    eqBy (\r -> headerHash r) x y && eqBy (\r -> payload r) x y

instance Eq Chain where
  Genesis == Genesis = True
  ChainBlock b c == ChainBlock b' c' = b == b' && c == c'
  _ == _ = False

tipHash :: Chain -> Hash Block
tipHash Genesis = genesisHash
tipHash (ChainBlock block _) = hash block

instance Eq Message where
  NewChain x == NewChain y = x == y
  NewVote x == NewVote y = x == y
  NewCertificate x == NewCertificate y = x == y
  _ == _ = False
