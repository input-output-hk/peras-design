module Peras.QCD.Crypto.Placeholders where

open import Haskell.Prelude
open import Peras.QCD.Crypto
open import Peras.QCD.Types
open import Peras.QCD.Types.Instances

{-# FOREIGN AGDA2HS
import Numeric.Natural (Natural)
import Peras.QCD.Types.Instances ()
zero :: Natural
zero = 0
#-}

-- Placeholders for cryptographic functions.

proveLeader : Slot → PartyId → LeadershipProof
proveLeader s p = MakeLeadershipProof (hashBytes (hash iPairHashable (s , p)))
{-# COMPILE AGDA2HS proveLeader #-}

signBlock : Slot → PartyId → Hash Block → Maybe Certificate → List Tx → Block
signBlock s p h c txs =
  record
    {
      slot = s
    ; creator = p
    ; parent = h
    ; certificate = c
    ; leadershipProof = proveLeader s p
    ; signature = MakeSignature (hashBytes (
                    hash iTripletHashable (
                        hash iPairHashable (s , p)
                      , hash iPairHashable (h , c)
                      , hash iListHashable txs
                      )
                    )
                  )
    ; bodyHash = hash iListHashable txs
    }
{-# COMPILE AGDA2HS signBlock #-}

SignVote : Set
SignVote = Round → PartyId → Hash Block → Vote
{-# COMPILE AGDA2HS SignVote #-}

buildCertificate : List Vote → Certificate
buildCertificate votes' =
  record {
    certificateRound = getRound votes'
  ; certificateBlock = getBlock votes'
  ; certificateBytes = hashBytes (hash iListHashable votes')
  }
  where
    getRound : List Vote → Round
    getRound [] = zero
    getRound (vote ∷ _) = voteRound vote
    getBlock : List Vote → Hash Block
    getBlock [] = genesisHash
    getBlock (vote ∷ _) = voteBlock vote
{-# COMPILE AGDA2HS buildCertificate #-}
