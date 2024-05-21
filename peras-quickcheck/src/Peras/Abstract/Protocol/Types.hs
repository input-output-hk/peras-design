module Peras.Abstract.Protocol.Types where

import Data.Time.Clock (UTCTime)
import Peras.Block (Block, Certificate, Party)
import Peras.Chain (Vote)
import Peras.Crypto (Hash, LeadershipProof)
import Peras.Numbering (RoundNumber)

-- | Bundle the handling of voting events and access to the vote API.
type VotingComponent m = VotingCallback m -> VoteApi m -> m ()

-- | Invoke a voting component.
type VotingCallback m = VotingEvent -> m ()

-- | There is only one type of voting event.
data VotingEvent = Voting
  { round :: RoundNumber
  -- ^ The round being voted upon.
  , leadership :: Maybe LeadershipProof
  -- ^ The leadership proof, if the party is a membership of the committee.
  }

-- | API for voting queries to other components such as the node.
data VoteApi m = VoteApi
  { preagreement :: RoundNumber -> Party -> LeadershipProof -> m (Maybe Block)
  -- ^ Call the preagreement procedure to find the candidate block being voted upon.
  , latestCertSeen :: UTCTime -> m Certificate
  -- ^ The latest certificate seen, as of the time specified.
  , latestCertOnChain :: UTCTime -> m Certificate
  -- ^ The latest certificate on the preferred chain, as of the time specified.
  , blockExtends :: UTCTime -> Block -> Certificate -> m Bool
  -- ^ Whether the block extends the block certified by the certificate, as of the time specified.
  , recordVote :: Vote -> m ()
  -- ^ Record a vote in the node's database.
  , diffuseVote :: Vote -> m ()
  -- ^ Diffuse a new vote.
  }

-- | Cryptography API.
data CryptoApi m = CryptoApi
  { signVote :: RoundNumber -> Party -> Hash Block -> LeadershipProof -> m Vote
  -- ^ Sign a vote.
  }
