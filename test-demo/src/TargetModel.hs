module TargetModel where

import Test.QuickCheck
import Test.QuickCheck.StateModel

-- Super simple protocol:
--  - The hosts take turns round robin to produce blocks.
--  - `blockIndex` is incremented with each block on the chain.
--  - Nodes have three "ticks" to produce a block
-- Network model:
--  - messages diffuse over the network instantly to all other
--    hosts.

newtype Block = Block { blockIndex :: Integer }
  deriving (Ord, Eq, Show, Generic)

data Host = Alice
          | Bob
          deriving (Ord, Eq, Show, Generic)

data Message = Message { messageBlock      :: Block
                       , messageOriginator :: Host
                       } deriving (Ord, Eq, Show, Generic)

-- StateModel -------------------------------------------------------------

data EnvState = EnvState { lastBlock :: Block
                         , sutHost   :: Host
                         , time      :: Integer
                         } deriving (Ord, Eq, Show, Generic)

deriving instance Show (Action EnvState a)

instance HasVariables (Action EnvState a) where
  getAllVariables (ProduceBlock b) = getAllVariables b
  getAllVariables Tick = mempty

instance StateModel EnvState where
  data Action EnvState a where
    ProduceBlock :: Block -> Action EnvState ()
    -- ^ The environment produces a block
    Tick :: Action EnvState ()
    -- ^ Time progresses by one unit

  initialState = EnvState { lastBlock = Block 0
                          , sutHost   = Alice
                          , time      = 0
                          }

  nextState s (ProduceBlock b) _ = s { lastBlock = b }
  nextState s Tick             _ = s { time = time s + 1 }


-- Implementation ---------------------------------------------------------

data Node m = Node { nodeSendTo              :: Message -> m ()
                   , nodeReceiveFrom         :: m [Message]
                   , nodeObserveCurrentBlock :: m Block
                   }
