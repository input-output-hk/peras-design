module Peras.QCD.Crypto.Placeholders where

import Peras.QCD.Crypto (Hash (hashBytes), Hashable (hash))
import Peras.QCD.Types (Block (MakeBlock), Certificate (MakeCertificate), LeadershipProof (MakeLeadershipProof), MembershipProof (MakeMembershipProof), PartyId, Round, Signature (MakeSignature), Slot, Tx, Vote (MakeVote, voteBlock, voteRound), Weight, genesisHash)

import Numeric.Natural (Natural)
import Peras.QCD.Types.Instances ()

zero :: Natural
zero = 0

proveLeader :: Slot -> PartyId -> LeadershipProof
proveLeader s p = MakeLeadershipProof (hashBytes (hash (s, p)))

signBlock ::
  Slot -> PartyId -> Hash Block -> Maybe Certificate -> [Tx] -> Block
signBlock s p h c txs =
  MakeBlock
    s
    p
    h
    c
    (proveLeader s p)
    ( MakeSignature
        (hashBytes (hash (hash (s, p), hash (h, c), hash txs)))
    )
    (hash txs)

signVote :: Round -> PartyId -> Weight -> Block -> Vote
signVote r p w b =
  MakeVote
    r
    p
    w
    (hash b)
    (MakeMembershipProof (hashBytes (hash (r, p))))
    (MakeSignature (hashBytes (hash (r, p, b))))

buildCertificate :: [Vote] -> Certificate
buildCertificate votes' =
  MakeCertificate
    (getRound votes')
    (getBlock votes')
    (hashBytes (hash votes'))
 where
  getRound :: [Vote] -> Round
  getRound [] = zero
  getRound (vote : _) = voteRound vote
  getBlock :: [Vote] -> Hash Block
  getBlock [] = genesisHash
  getBlock (vote : _) = voteBlock vote
