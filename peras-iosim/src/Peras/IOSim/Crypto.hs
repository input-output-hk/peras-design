module Peras.IOSim.Crypto (
  VrfOutput,
  VrfUsage (..),
  committeMemberRandom,
  nextVrf,
  proveLeadership,
  proveMembership,
  randomBytes,
  signBlock,
  signVote,
  slotLeaderRandom,
  uniformRandom,
) where

import Peras.Crypto (LeadershipProof (LeadershipProof), MembershipProof (MembershipProof), Signature (Signature))
import System.Random (mkStdGen, uniformR)

import Data.ByteString as BS

type VrfOutput = Double

nextVrf :: VrfOutput -> VrfOutput
nextVrf x =
  fst
    . uniformR (0, 1)
    . mkStdGen
    . fromIntegral
    . fst
    $ decodeFloat x

data VrfUsage
  = VrfSlotLeader
  | VrfCommitteeMember
  | VrfLeadershipProof
  | VrfMembershipProof
  | VrfBlockSignature
  | VrfVoteSignature
  | VrfBodyHash
  deriving (Bounded, Enum, Eq, Ord, Read, Show)

uniformRandom ::
  VrfUsage ->
  VrfOutput ->
  Double
uniformRandom usage vrf =
  let
    b = 10
    x = b ^ fromEnum usage * vrf
   in
    x - fromIntegral (floor x :: Integer)

randomBytes ::
  VrfUsage ->
  VrfOutput ->
  BS.ByteString
randomBytes usage vrf =
  let
    bytes 0 _ = BS.empty
    bytes n x =
      let
        y = 256 * x
        y' = floor y
       in
        BS.singleton y' <> bytes (n - 1 :: Int) (y - fromIntegral y')
   in
    bytes 6 $ uniformRandom usage vrf

slotLeaderRandom ::
  VrfOutput ->
  Double
slotLeaderRandom = uniformRandom VrfSlotLeader

committeMemberRandom ::
  VrfOutput ->
  Double
committeMemberRandom = uniformRandom VrfCommitteeMember

signBlock ::
  VrfOutput ->
  a ->
  Signature
signBlock vrf _ = Signature $ randomBytes VrfBlockSignature vrf

signVote ::
  VrfOutput ->
  a ->
  Signature
signVote vrf _ = Signature $ randomBytes VrfVoteSignature vrf

proveLeadership ::
  VrfOutput ->
  a ->
  LeadershipProof
proveLeadership vrf _ = LeadershipProof $ randomBytes VrfLeadershipProof vrf

proveMembership ::
  VrfOutput ->
  a ->
  MembershipProof
proveMembership vrf _ = MembershipProof $ randomBytes VrfMembershipProof vrf
