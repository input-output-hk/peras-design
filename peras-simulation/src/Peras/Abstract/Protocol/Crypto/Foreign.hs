module Peras.Abstract.Protocol.Crypto.Foreign where

import Data.Functor.Identity (Identity (runIdentity))
import qualified Data.Hashable as H (Hashable (..))
import qualified Data.Set as Set (fromList)
import qualified Peras.Abstract.Protocol.Crypto as C
import Peras.Abstract.Protocol.Params (PerasParams)
import Peras.Abstract.Protocol.Types (PerasResult)
import Peras.Block (Block, Certificate, Party, PartyId, Payload)
import Peras.Chain (Vote, VotingWeight)
import Peras.Crypto (Hash, LeadershipProof, MembershipProof, Signature)
import Peras.Numbering (RoundNumber, SlotNumber)

type IsSlotLeader = Bool

type IsCommitteeMember = Bool

mkPure :: Identity (PerasResult a) -> a
mkPure = either (error . show) id . runIdentity

createSignedBlock :: Party -> SlotNumber -> Hash Block -> Maybe Certificate -> LeadershipProof -> Hash Payload -> Block
createSignedBlock pa sn hb mc lp hp = mkPure $ C.createSignedBlock pa sn hb mc lp hp

createSignedCertificate :: Party -> [Vote] -> Certificate
createSignedCertificate pa vos = mkPure $ C.createSignedCertificate pa (Set.fromList vos)

createSignedVote :: Party -> RoundNumber -> Hash Block -> MembershipProof -> VotingWeight -> Vote
createSignedVote pa rn hb mp vw = mkPure $ C.createSignedVote pa rn hb mp vw

createLeadershipProof :: SlotNumber -> [Party] -> LeadershipProof
createLeadershipProof sn pas = mkPure $ C.createLeadershipProof sn (Set.fromList pas)

createMembershipProof :: RoundNumber -> [Party] -> MembershipProof
createMembershipProof rn pas = mkPure $ C.createMembershipProof rn (Set.fromList pas)

checkSignedBlock :: Block -> Bool
checkSignedBlock _ = True

checkSignedCertificate :: Certificate -> Bool
checkSignedCertificate _ = True

checkSignedVote :: Vote -> Bool
checkSignedVote _ = True

checkLeadershipProof :: LeadershipProof -> Bool
checkLeadershipProof _ = True

sign :: H.Hashable a => a -> Signature
sign = C.sign

mkParty :: PartyId -> [SlotNumber] -> [RoundNumber] -> Party
mkParty = C.mkParty

mkSlotLeader :: Party -> SlotNumber -> IsSlotLeader -> Party
mkSlotLeader = C.mkSlotLeader

mkCommitteeMember :: Party -> PerasParams -> SlotNumber -> IsCommitteeMember -> Party
mkCommitteeMember = C.mkCommitteeMember
