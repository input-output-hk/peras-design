module Peras.Chain where

import Numeric.Natural (Natural)
import Peras.Block (Block, PartyId)
import Peras.Crypto (Hash, MembershipProof, Signature)

newtype RoundNumber = MkRoundNumber {roundNumber :: Natural}
  deriving (Eq)

data Vote = MkVote
  { votingRound :: RoundNumber
  , creatorId :: PartyId
  , committeeMembershipProof :: MembershipProof
  , blockHash :: Hash Block
  , signature :: Signature
  }
  deriving (Eq)

type Chain = [Block]

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
