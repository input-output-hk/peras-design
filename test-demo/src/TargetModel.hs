module TargetModel where

import Data.Maybe
import Data.IORef
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Test.QuickCheck
import Test.QuickCheck.StateModel
import Test.QuickCheck.Monadic
import Test.QuickCheck.Extras

import CommonTypes
import Model

-- Super simple protocol:
--  - The hosts take turns round robin to produce blocks.
--  - `blockIndex` is incremented with each block on the chain.
--  - If a node misses its window the other node should produce the missed block in its slot
--    instead.
-- Network model:
--  - messages diffuse over the network instantly to all other
--    hosts.

-- TODO: the current model doesn't increment the blocks because negative actions
-- (specifically negative `Tick`s!) mean that sometimes the environment (dishonestly)
-- fails to trasmit a message! That means the chain isn't unbroken. However, we don't
-- detect that safety property here because we aren't observing the fact that when the
-- sut sends a message it always sends the message that contains the slot number, not the
-- increment of the last message we received. Something to think about here.

-- The assumption is that honest nodes behave deterministically based on their view of the world.
-- This means that we can predictibly reject dishonest nodes, and the environment does not need any
-- runtime information from the node to know what are valid behaviours. Furthermore, dishonest
-- behaviour *can* be nondeterministic, but is only introduced by the environment and thus is known
-- at generation time. For example, there can be voting in the protocol, but there is always a
-- *correct* vote for each node given their local information. This means that we can predict the
-- result of a vote at generation time provided the sut node votes honestly, and fail the test if it
-- does not.

-- How do we connect this to the Agda specification? Idea: this model doesn't specify exactly what
-- the node under test does, so what we might do is prove that given a trace from this model
-- completed with specific valid actions of the node we can reconstruct a valid trace in the
-- specification.

-- Talking to Arnaud: honest nodes are determinstic in the sense that we know exactly what they will
-- do at any point.

-- newtype Block = Block { blockIndex :: Integer }
--   deriving (Ord, Eq, Show, Generic)

-- data Party = Alice
--           | Bob
--           deriving (Ord, Eq, Show, Generic)

-- StateModel -------------------------------------------------------------

-- data EnvState = EnvState { lastBlock :: Block
--                          -- ^ the last block anyone sent
--                          , lastBlockTime :: Integer
--                          -- ^ the time at which the last block was sent
--                          , sutParty :: Party
--                          -- ^ the host of the system under test
--                          , time :: Integer
--                          -- ^ the current time
--                          } deriving (Ord, Eq, Show, Generic)

-- data Signal = ProduceBlock Block
--             | Tick
--             | DishonestProduceBlock Block
--             | DishonestTick
--             deriving (Ord, Eq, Show, Generic)

-- preProduceBlock :: EnvState -> Block -> Bool
-- preProduceBlock s@EnvState{..} b =
--   and [ nextBlock s == b
--       , whoseSlot s == envParty s
--       , lastBlockTime /= time
--       ]

-- step :: EnvState -> Signal -> Maybe (EnvState, [Block])
-- step s@EnvState{..} = \case
--   ProduceBlock b
--     | preProduceBlock s b -> Just (s { lastBlock = b, lastBlockTime = time }, [])

--   Tick
--     -- We've already sent our message
--     | whoseSlot s == envParty s
--     , lastBlockTime == time -> Just (s{time = time + 1}, [])
--     -- Genesis
--     | time == 0 -> Just (s { time = time + 1 }, [])
--     -- The other party will send their message
--     | whoseSlot s == sutParty -> Just (s { time = time + 1
--                                         , lastBlock = nextBlock s
--                                         , lastBlockTime = time
--                                         }
--                                      , [nextBlock s])

--   DishonestProduceBlock b
--     | not $ preProduceBlock s b -> Just (s, [])

--   DishonestTick
--     | whoseSlot s == envParty s
--     , lastBlockTime < time -> Just (s{time = time + 1}, [])

--   _ -> Nothing

-- envParty :: EnvState -> Party
-- envParty EnvState{..} = case sutParty of
--   Alice -> Bob
--   Bob -> Alice

-- nextBlock :: EnvState -> Block
-- nextBlock EnvState{..} = Block $ blockIndex lastBlock + 1

-- whoseSlot :: EnvState -> Party
-- whoseSlot EnvState{..} = whoseSlotTime time

instance Show (Action EnvState a) where
  show (Step sig) = show sig
deriving instance Eq (Action EnvState a)

instance HasVariables (Action EnvState a) where
  getAllVariables (Step sig) = getAllVariables sig

instance StateModel EnvState where
  data Action EnvState a where
    Step :: Signal -> Action EnvState [Block]

  initialState = startingState

  nextState s (Step sig) _ = maybe s fst $ step s sig

  precondition s (Step sig) = step s sig /= Nothing

  arbitraryAction ctx s =
    frequency
      [ (10, pure $ Some $ Step Tick)
      , (10, pure $ Some $ Step $ ProduceBlock $ nextBlock s)
      -- , (5, Some . Step . DishonestProduceBlock . Block <$> arbitrary)
      -- , (5, pure $ Some $ Step DishonestTick)
      ]

-- Run Model -----------------------------------------------------------

data Node m = Node { nodeSendTo :: Party -> Block -> m ()
                   , nodeReceiveFrom :: m [Block]
                   , nodeProgressTime :: m ()
                   }

type ModelMonad m = ReaderT (Node m) m

onNode :: Monad m => (Node m -> m a) -> ModelMonad m a
onNode f = ask >>= lift . f

instance (Monad m, Realized m () ~ (), Realized m [Block] ~ [Block]) => RunModel EnvState (ModelMonad m) where
  perform s@MkEnvState{..} (Step a) _ = case a of
    Tick -> do
      msgs <- onNode nodeReceiveFrom
      onNode nodeProgressTime
      pure msgs
    -- DishonestTick -> do
    --   msgs <- onNode nodeReceiveFrom
    --   onNode nodeProgressTime
    --   pure msgs
    ProduceBlock b -> do
      onNode $ \ sut -> nodeSendTo sut (envParty s) b
      pure []
    -- DishonestProduceBlock b -> do
    --   onNode $ \ sut -> nodeSendTo sut (envParty s) b
    --   pure []

  postcondition (sBefore, _) (Step sig) _ msgs =
    case step sBefore sig of
      Just (_, expected) -> do
        counterexamplePost $ unlines ["Expected messages:", "  " ++ show expected, "got:", "  " ++ show msgs]
        pure $ expected == msgs
      Nothing -> pure True

prop_nodeCorrect :: (Monad m, RunModel EnvState (ModelMonad m))
                  => Node m
                  -> (PropertyM m () -> Property)
                  -> Actions EnvState
                  -> Property
prop_nodeCorrect node runProp as = runProp $ do
  () <$ runPropertyReaderT (runActions as) node

-- Honest implementation --------------------------------------------------

whoseSlotTime :: Integer -> Party
whoseSlotTime time
  | even time = Alice
  | otherwise = Bob

prop_honest :: Actions EnvState -> Property
prop_honest = prop_nodeCorrect (honestNode Alice) runHonestMonad

data HonestNodeState = HonestNodeState
  { honestNodeClock     :: IORef Integer
  , honestNodeLastBlock :: IORef Integer
  , honestNodeLastRecvTime :: IORef Integer
  , honestNodeLastSendTime :: IORef Integer
  }

type HonestNodeMonad = ReaderT HonestNodeState IO

runHonestMonad :: PropertyM HonestNodeMonad () -> Property
runHonestMonad m = monadicIO $ do
  clock <- lift $ newIORef 0
  block <- lift $ newIORef 0
  rstamp <- lift $ newIORef 0
  sstamp <- lift $ newIORef 0
  runPropertyReaderT m $ HonestNodeState clock block rstamp sstamp

honestNode :: Party -> Node HonestNodeMonad
honestNode h = Node{..}
  where nodeSendTo sender (Blk n) = do
          block <- asks honestNodeLastBlock
          clock <- asks honestNodeClock
          rstamp <- asks honestNodeLastRecvTime
          time     <- lift $ readIORef clock
          lastSeen <- lift $ readIORef block
          lastRecv <- lift $ readIORef rstamp
          let validBlock = n == lastSeen + 1 && sender == whoseSlotTime time && lastRecv < time
          when validBlock $ do
            lift $ writeIORef rstamp time
            lift $ writeIORef block n
        nodeReceiveFrom = do
          clock <- asks honestNodeClock
          block <- asks honestNodeLastBlock
          tstamp <- asks honestNodeLastSendTime
          time <- lift $ readIORef clock
          n    <- lift $ readIORef block
          ts   <- lift $ readIORef tstamp
          let shouldSend = h == whoseSlotTime time && time > ts
          when shouldSend $ do
            lift $ writeIORef block (n + 1)
            lift $ writeIORef tstamp time
          pure [ Blk $ n + 1 | shouldSend ]
        nodeProgressTime = do
          clock <- asks honestNodeClock
          lift $ modifyIORef clock (+1)

