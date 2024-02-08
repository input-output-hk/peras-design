module Peras.Crypto where

import Data.ByteString as BS

newtype Hash = Hash{hash :: ByteString}

newtype MembershipProof = MembershipProof{proofM :: ByteString}

newtype LeadershipProof = LeadershipProof{proof :: ByteString}

newtype Signature = Signature{signature :: ByteString}

newtype VerificationKey = VerificationKey{verificationKey ::
                                          ByteString}

