module Peras.QCD.Types.Instances where

open import Haskell.Prelude
open import Peras.QCD.Crypto
open import Peras.QCD.Types
open import Peras.QCD.Util using (eqBy; eqByBS)

{-# FOREIGN AGDA2HS
{-# OPTIONS_GHC -fno-warn-orphans #-}
#-}

-- Instances.

instance
  iMembershipProofEq : Eq MembershipProof
  iMembershipProofEq ._==_ = eqByBS membershipProofBytes
{-# COMPILE AGDA2HS iMembershipProofEq #-}

instance
  iMembershipProofHashable : Hashable MembershipProof
  iMembershipProofHashable .hash = castHash ∘ hash iByteStringHashable ∘ membershipProofBytes
{-# COMPILE AGDA2HS iMembershipProofHashable #-}

instance
  iLeadershipProofEq : Eq LeadershipProof
  iLeadershipProofEq ._==_ = eqByBS leadershipProofBytes
{-# COMPILE AGDA2HS iLeadershipProofEq #-}

instance
  iLeadershipProofHashable : Hashable LeadershipProof
  iLeadershipProofHashable .hash = castHash ∘ hash iByteStringHashable ∘ leadershipProofBytes
{-# COMPILE AGDA2HS iLeadershipProofHashable #-}

instance
  iSignatureEq : Eq Signature
  iSignatureEq ._==_ = eqByBS signatureBytes
{-# COMPILE AGDA2HS iSignatureEq #-}

instance
  iSignatureHashable : Hashable Signature
  iSignatureHashable .hash = castHash ∘ hash iByteStringHashable ∘ signatureBytes
{-# COMPILE AGDA2HS iSignatureHashable #-}

instance
  iVerificationKeyEq : Eq VerificationKey
  iVerificationKeyEq ._==_ = eqByBS verificationKeyBytes
{-# COMPILE AGDA2HS iVerificationKeyEq #-}

instance
  iVerificationKeyHashable : Hashable VerificationKey
  iVerificationKeyHashable .hash = castHash ∘ hash iByteStringHashable ∘ verificationKeyBytes
{-# COMPILE AGDA2HS iVerificationKeyHashable #-}

instance
  iVoteEq : Eq Vote
  iVoteEq ._==_ x y = eqBy voteRound x y
                        && eqBy voteParty x y
                        && eqBy voteBlock x y
                        && eqBy voteProof x y
                        && eqBy voteSignature x y
{-# COMPILE AGDA2HS iVoteEq #-}

instance
  iVoteHashable : Hashable Vote
  iVoteHashable .hash = castHash ∘ hash iMembershipProofHashable ∘ voteProof
{-# COMPILE AGDA2HS iVoteHashable #-}

instance
  iCertificateEq : Eq Certificate
  iCertificateEq ._==_ x y = eqBy certificateRound x y
                               && eqBy certificateBlock x y
                               && eqByBS certificateBytes x y
{-# COMPILE AGDA2HS iCertificateEq #-}

instance
  iCertificateHashable : Hashable Certificate
  iCertificateHashable .hash x =
    castHash $ hash iTripletHashable
      (certificateRound x , certificateBlock x , certificateBytes x)
{-# COMPILE AGDA2HS iCertificateHashable #-}

instance
  iBlockEq : Eq Block
  iBlockEq ._==_ x y = eqBy slot x y
                         && eqBy creator x y
                         && eqBy parent x y
                         && eqBy certificate x y
                         && eqBy leadershipProof x y
                         && eqBy signature x y
                         && eqBy bodyHash x y
{-# COMPILE AGDA2HS iBlockEq #-}

instance
  iBlockHashable : Hashable Block
  iBlockHashable .hash = castHash ∘ hash iSignatureHashable ∘ signature
{-# COMPILE AGDA2HS iBlockHashable #-}

instance
  iBlockBodyEq : Eq BlockBody
  iBlockBodyEq ._==_ x y = eqBy headerHash x y && eqBy payload x y
{-# COMPILE AGDA2HS iBlockBodyEq #-}

instance
  iChainEq : Eq Chain
  iChainEq ._==_ Genesis Genesis = True
  iChainEq ._==_ (ChainBlock b c) (ChainBlock b' c') = b == b' && c == c'
  iChainEq ._==_ _ _ = False
{-# COMPILE AGDA2HS iChainEq #-}

tipHash : Chain → Hash Block
tipHash Genesis = genesisHash
tipHash (ChainBlock block _) = hash iBlockHashable block
{-# COMPILE AGDA2HS tipHash #-}

instance
  iMessageEq : Eq Message
  iMessageEq ._==_ (NewChain x) (NewChain y) = x == y
  iMessageEq ._==_ (NewVote x) (NewVote y) = x == y
  iMessageEq ._==_ _ _ = False
{-# COMPILE AGDA2HS iMessageEq #-}
