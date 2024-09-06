{-# LANGUAGE DeriveGeneric #-}

module Peras.Chain where

import Numeric.Natural (Natural)
import Peras.Block (Block, Certificate, PartyId)
import Peras.Crypto (Hash, MembershipProof, Signature)
import Peras.Numbering (RoundNumber)

import GHC.Generics (Generic)

type VotingWeight = Natural

data Vote = MkVote
  { votingRound :: RoundNumber
  , creatorId :: PartyId
  , proofM :: MembershipProof
  , blockHash :: Hash Block
  , signature :: Signature
  }
  deriving (Generic)

instance Eq Vote where
  x == y =
    votingRound x == votingRound y
      && creatorId x == creatorId y
      && proofM x == proofM y
      && blockHash x == blockHash y
      && signature x == signature y

type Chain = [Block]

insertCert :: Certificate -> [Certificate] -> [Certificate]
insertCert cert [] = [cert]
insertCert cert (cert' : certs) =
  if cert == cert'
    then cert' : certs
    else cert' : insertCert cert certs

foldl1Maybe :: (a -> a -> a) -> [a] -> Maybe a
foldl1Maybe f xs =
  foldl
    ( \m y ->
        Just
          ( case m of
              Nothing -> y
              Just x -> f x y
          )
    )
    Nothing
    xs

prefix :: [Block] -> [Block] -> [Block] -> [Block]
prefix acc (x : xs) (y : ys) =
  if x == y then prefix (x : acc) xs ys else reverse acc
prefix acc _ _ = reverse acc

commonPrefix :: [Chain] -> [Block]
commonPrefix chains =
  case listPrefix of
    Nothing -> []
    Just bs -> reverse bs
 where
  listPrefix :: Maybe [Block]
  listPrefix = foldl1Maybe (prefix []) (map reverse chains)
