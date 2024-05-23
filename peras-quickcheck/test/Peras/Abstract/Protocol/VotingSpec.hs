module Peras.Abstract.Protocol.VotingSpec where

import Control.Concurrent.Class.MonadSTM (MonadSTM (readTVarIO), newTVarIO)
import Data.Either (isRight)
import qualified Data.Set as Set
import Peras.Abstract.Protocol.Diffusion (defaultDiffuser, diffuseVote, pendingVotes)
import Peras.Abstract.Protocol.Types (defaultParams, initialPerasState)
import Peras.Abstract.Protocol.Voting (voting)
import Peras.Arbitraries (generateWith)
import Peras.Block (Party (MkParty))
import Peras.Numbering (RoundNumber)
import Test.Hspec (Spec, it, shouldReturn, shouldSatisfy)
import Test.QuickCheck (arbitrary, generate)

spec :: Spec
spec =
  it "votes on preagreement's block given party is committee member" $ do
    block <- generate arbitrary
    let params = defaultParams
        roundNumber = 43
        party = committeeMemberFor roundNumber
        preagreement _ _ _ _ = pure $ Right $ Just (block, 1)
    perasState <- newTVarIO initialPerasState
    diffuser <- newTVarIO defaultDiffuser

    voting params party perasState roundNumber preagreement (diffuseVote diffuser) >>= (`shouldSatisfy` isRight)

    (Set.size . pendingVotes <$> readTVarIO diffuser) `shouldReturn` 1

committeeMemberFor :: RoundNumber -> Party
committeeMemberFor roundNumber =
  MkParty (fromIntegral roundNumber) (arbitrary `generateWith` 42)
