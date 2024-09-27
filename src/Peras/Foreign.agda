module Peras.Foreign where

open import Haskell.Prelude
open import Peras.Block
open import Peras.Chain
open import Peras.Conformance.Params
open import Peras.Crypto
open import Peras.Numbering


{-# FOREIGN AGDA2HS
  {-# OPTIONS_GHC -fno-warn-missing-pattern-synonym-signatures #-}
  {-# OPTIONS_GHC -fno-warn-missing-signatures #-}
  {-# OPTIONS_GHC -fno-warn-name-shadowing #-}
  {-# OPTIONS_GHC -fno-warn-type-defaults #-}
  {-# OPTIONS_GHC -fno-warn-unused-imports #-}
  {-# OPTIONS_GHC -fno-warn-unused-matches #-}
  import Data.Functor.Identity ( Identity(runIdentity) )
  import Peras.Block ( Block, Certificate, Party, PartyId, Payload )
  import Peras.Chain ( Vote, VotingWeight )
  import Peras.Conformance.Params ( PerasParams )
  import Peras.Crypto ( Hash, LeadershipProof, MembershipProof, Signature )
  import Peras.Numbering ( RoundNumber, SlotNumber )
  import Peras.Prototype.Types (PerasResult)
  import qualified Data.Set as Set (fromList)
  import qualified Data.Hashable as H (Hashable (..))
  import qualified Peras.Prototype.Crypto as C
#-}

IsSlotLeader = Bool

{-# COMPILE AGDA2HS IsSlotLeader #-}

IsCommitteeMember = Bool

{-# COMPILE AGDA2HS IsCommitteeMember #-}

postulate

  createSignedBlock
    : Party
    → SlotNumber
    → Hash Block
    → Maybe Certificate
    → LeadershipProof
    → Hash Payload
    → Block

  createSignedCertificate
    : Party
    → List Vote
    → Certificate
    
  createSignedVote
    : Party
    → RoundNumber
    → Hash Block
    → MembershipProof
    → VotingWeight
    → Vote
    
  createLeadershipProof
    : SlotNumber
    → List Party
    → LeadershipProof
    
  createMembershipProof
    : RoundNumber
    → List Party
    → MembershipProof
    
  checkSignedBlock : Block → Bool
  
  checkSignedVote : Vote → Bool
  
  checkLeadershipProof : LeadershipProof → Bool
  
  checkMembershipProof : MembershipProof → Bool
  
  sign : {a : Set} → ⦃ _ : Hashable a ⦄ → a -> Signature

  mkParty : PartyId → List SlotNumber -> List RoundNumber -> Party

  mkSlotLeader : Party → SlotNumber → IsSlotLeader → Party

  mkCommitteeMember : Party → PerasParams → SlotNumber → IsCommitteeMember → Party

{-# FOREIGN AGDA2HS

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

#-}
