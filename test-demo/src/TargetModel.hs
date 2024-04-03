module TargetModel where

import Data.IORef
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Test.QuickCheck
import Test.QuickCheck.StateModel
import Test.QuickCheck.Monadic
import Test.QuickCheck.Extras

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

newtype Block = Block { blockIndex :: Integer }
  deriving (Ord, Eq, Show, Generic)

data Host = Alice
          | Bob
          deriving (Ord, Eq, Show, Generic)

data Message = Message { messageBlock      :: Block
                       , messageOriginator :: Host
                       } deriving (Ord, Eq, Show)

-- StateModel -------------------------------------------------------------

data EnvState = EnvState { lastBlock :: Block
                         -- ^ the last block anyone sent
                         , lastBlockTime :: Integer
                         -- ^ the time at which the last block was sent
                         , sutHost :: Host
                         -- ^ the host of the system under test
                         , time :: Integer
                         -- ^ the current time
                         } deriving (Ord, Eq, Show, Generic)

deriving instance Show (Action EnvState a)
deriving instance Eq (Action EnvState a)

instance HasVariables (Action EnvState a) where
  getAllVariables (ProduceBlock b) = getAllVariables b
  getAllVariables (ProduceInvalidBlock b) = getAllVariables b
  getAllVariables Tick = mempty
  getAllVariables TickInvalid = mempty

envHost :: EnvState -> Host
envHost EnvState{..} = case sutHost of
  Alice -> Bob
  Bob -> Alice

nextBlock :: EnvState -> Block
nextBlock EnvState{..} = Block $ blockIndex lastBlock + 1

whoseSlot :: Integer -> Host
whoseSlot time
  | even time = Alice
  | otherwise = Bob

expectedMessage :: EnvState -> Message
expectedMessage s = Message (nextBlock s) $ whoseSlot (time s)

instance StateModel EnvState where
  data Action EnvState a where
    -- *** Honest actions ***
    ProduceBlock :: Block -> Action EnvState ()
    -- ^ The environment produces a block
    Tick :: Action EnvState [Message]
    -- ^ Time progresses by one unit

    -- *** Dishonest actions ***
    ProduceInvalidBlock :: Block -> Action EnvState ()
    -- ^ The environment produces an invalid block
    TickInvalid :: Action EnvState [Message]
    -- ^ Tick when you should be sending a block

  initialState = EnvState { lastBlock = Block (-1)
                          , lastBlockTime = (-1)
                          , sutHost = Alice
                          , time    = (-1)
                          }

  nextState s (ProduceBlock b) _ = s { lastBlock = b
                                     , lastBlockTime = time s }
  nextState s Tick             _ = modifyBlock $ s { time = time s + 1 }
    where modifyBlock s'
            -- Assume the SUT behaves honestly
            | sutHost s' == whoseSlot (time s') = s' { lastBlock = nextBlock s
                                                     , lastBlockTime = time s'
                                                     }
            | otherwise = s'
  nextState s TickInvalid v = nextState s Tick v
  nextState s ProduceInvalidBlock{} _ = s

  precondition s@EnvState{..} = \case
    -- An honest environment can only tick when it has fulfilled
    -- its obligation to produce a block
    Tick
      -- We've already sent our message
      | whoseSlot time == envHost s
      , lastBlockTime == time -> True
      -- The other party will send their message
      | whoseSlot (time + 1) == envHost s -> True
    -- An honest environment can produce a block once on its own turn
    ProduceBlock b
      | expectedMessage s == Message b (envHost s)
      , lastBlockTime /= time -> True
    -- A dishonest block is simply a block that is not allowed
    ProduceInvalidBlock b -> not $ precondition s $ ProduceBlock b
    -- Dishonestly ignoring time
    TickInvalid
      | whoseSlot time == envHost s
      , lastBlockTime < time -> True
    -- Nothing else is allowed
    _ -> False

  arbitraryAction ctx s =
    frequency
      [ (10, pure $ Some Tick)
      , (10, pure $ Some $ ProduceBlock $ nextBlock s)
      , (5, Some . ProduceInvalidBlock . Block <$> arbitrary)
      , (5, pure $ Some TickInvalid)
      ]

-- Run Model --------------------------------------------------------------

data Node m = Node { nodeSendTo :: Message -> m ()
                   , nodeReceiveFrom :: m [Message]
                   , nodeProgressTime :: m ()
                   }

type ModelMonad m = ReaderT (Node m) (StateT Block m)

onNode :: Monad m => (Node m -> m a) -> ModelMonad m a
onNode f = ask >>= lift . lift . f

instance (Monad m, Realized m () ~ (), Realized m [Message] ~ [Message]) => RunModel EnvState (ModelMonad m) where
  perform s@EnvState{..} a _ = case a of
    Tick -> do
      onNode nodeProgressTime
      onNode nodeReceiveFrom
    TickInvalid -> do
      onNode nodeProgressTime
      onNode nodeReceiveFrom
    ProduceBlock b -> do
      when (expectedMessage s == Message b (envHost s)) $ do
        put b
      onNode $ flip nodeSendTo $ Message b (envHost s)
    ProduceInvalidBlock b -> do
      onNode $ flip nodeSendTo $ Message b (envHost s)

  postcondition (sBefore, sAfter) Tick _ msgs = do
    monitorPost $ counterexample $ "Received " ++ show msgs ++ " at time " ++ show (time sAfter)
    lastHonestBlock <- lift get
    case msgs of
      []
        | whoseSlot (time sAfter) == sutHost sAfter -> do
            counterexamplePost $ "Node failed to produce a block in time"
            pure False
        | otherwise -> pure True
      [m]
        | messageOriginator m /= sutHost sAfter -> do
            counterexamplePost $ "Node produced message with incorrect host " ++ show m
            pure False
        | messageBlock m /= nextBlock sBefore -> do
            counterexamplePost $
              unlines [ "Node produced a a message with incorrect block"
                      , "  " ++ show m
                      , "expected"
                      , "  " ++ show (nextBlock sBefore)
                      , "in before state"
                      , "  " ++ show sBefore
                      , "and after state"
                      , "  " ++ show sAfter
                      ]
            pure False
        | whoseSlot (time sAfter) /= sutHost sAfter -> do
            counterexamplePost $
              unlines [ "Node produced a message in the wrong slot"
                      , "  " ++ show m
                      ]
            pure False
        | messageBlock m == lastHonestBlock -> do
            counterexamplePost $ "Node produced the same block twice " ++ show m
            pure False
        | otherwise -> do
            lift $ put (messageBlock m)
            pure True
      _ -> do
        counterexamplePost $ "Node produced too many messages " ++ show msgs
        pure False
  postcondition tr TickInvalid lookup msgs = postcondition tr Tick lookup msgs
  postcondition (_, s@EnvState{..}) (ProduceBlock b) _ _ = do
    monitorPost $ counterexample $ "Environment sent " ++ show (Message b (envHost s)) ++ " at time " ++ show time
    pure True
  postcondition (_, s@EnvState{..}) (ProduceInvalidBlock b) _ _ = do
    monitorPost $ counterexample $ "Environment dishonestly sent " ++ show (Message b (envHost s)) ++ " at time " ++ show time
    pure True

prop_nodeCorrect :: (Monad m, RunModel EnvState (ModelMonad m))
                  => Node m
                  -> (PropertyM m () -> Property)
                  -> Actions EnvState
                  -> Property
prop_nodeCorrect node runProp as = runProp $ do
  () <$ runPropertyStateT (runPropertyReaderT (runActions as) node) (Block (-1))

-- Honest implementation --------------------------------------------------

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
  clock <- lift $ newIORef (-1)
  block <- lift $ newIORef (-1)
  rstamp <- lift $ newIORef (-1)
  sstamp <- lift $ newIORef (-1)
  runPropertyReaderT m $ HonestNodeState clock block rstamp sstamp

honestNode :: Host -> Node HonestNodeMonad
honestNode h = Node{..}
  where nodeSendTo (Message (Block n) sender) = do
          block <- asks honestNodeLastBlock
          clock <- asks honestNodeClock
          rstamp <- asks honestNodeLastRecvTime
          time     <- lift $ readIORef clock
          lastSeen <- lift $ readIORef block
          lastRecv <- lift $ readIORef rstamp
          let validBlock = n == lastSeen + 1 && sender == whoseSlot time && lastRecv < time
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
          let shouldSend = h == whoseSlot time && time > ts
          when shouldSend $ do
            lift $ writeIORef block (n + 1)
            lift $ writeIORef tstamp time
          pure [ Message (Block $ n + 1) h | shouldSend ]
        nodeProgressTime = do
          clock <- asks honestNodeClock
          lift $ modifyIORef clock (+1)

