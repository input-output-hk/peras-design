module Peras.QCD.Crypto.Placeholders where

import Peras.QCD.Crypto (Hash (hashBytes), Hashable (hash))
import Peras.QCD.Types (Block (MakeBlock), Certificate (MakeCertificate), LeadershipProof (MakeLeadershipProof), PartyId, Round, Signature (MakeSignature), Slot, Tx, Vote (voteBlock, voteRound), genesisHash)

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

type SignVote = Round -> PartyId -> Hash Block -> Vote

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
