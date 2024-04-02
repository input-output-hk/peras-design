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
--  - Nodes have three "ticks" to produce a block
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

data EnvState = EnvState { lastEnvBlock :: Block
                         -- ^ last block produced by the environment
                         , sutHost :: Host
                         -- ^ the host of the system under test
                         , time :: Integer
                         } deriving (Ord, Eq, Show, Generic)

deriving instance Show (Action EnvState a)
deriving instance Eq (Action EnvState a)

instance HasVariables (Action EnvState a) where
  getAllVariables (ProduceBlock b) = getAllVariables b
  getAllVariables Tick = mempty

environmentsTurn :: EnvState -> Bool
environmentsTurn EnvState{..}
  | blockIndex lastEnvBlock == slot = False
  | otherwise = case sutHost of
      Alice -> odd slot
      Bob -> even slot
  where slot = time `div` 3

envHost :: EnvState -> Host
envHost EnvState{..} = case sutHost of
  Alice -> Bob
  Bob -> Alice

nextEnvBlock :: EnvState -> Gen Block
nextEnvBlock EnvState{..} = pure $ Block (blockIndex lastEnvBlock + 2)

isNextEnvBlock :: EnvState -> Block -> Bool
isNextEnvBlock EnvState{..} b = blockIndex b == blockIndex lastEnvBlock + 2

isNextSutBlock :: EnvState -> Block -> Bool
isNextSutBlock EnvState{..} b = blockIndex b == blockIndex lastEnvBlock + 1

whoseSlot :: Integer -> Host
whoseSlot time
  | even (time `div` 3) = Alice
  | otherwise           = Bob

expectedMessage :: EnvState -> Message
expectedMessage EnvState{..} = Message (Block b) $ whoseSlot time
  where
    b | whoseSlot time == sutHost = blockIndex lastEnvBlock + 1
      | otherwise                 = blockIndex lastEnvBlock + 2

instance StateModel EnvState where
  data Action EnvState a where
    ProduceBlock :: Block -> Action EnvState ()
    -- ^ The environment produces a block
    Tick :: Action EnvState [Message]
    -- ^ Time progresses by one unit

  initialState = EnvState { lastEnvBlock = Block (-1)
                          , sutHost      = Alice
                          , time         = 0
                          }

  nextState s (ProduceBlock b) _ = s { lastEnvBlock = b }
  nextState s Tick             _ = s { time = time s + 1 }

  failureNextState s Tick = s { time = time s + 1 }
  failureNextState s _ = s

  precondition s@EnvState{..} = \case
    -- An honest environment can only tick when it has fulfilled
    -- its obligation to produce a block
    Tick
      -- It is not the environments turn to
      -- send a message
      | not $ environmentsTurn s -> True
      -- We are not on a slot boundry
      | time `mod` 3 < 2 -> True
    -- We can only produce a block if its the environments turn and
    -- the block it is producing is the next block.
    ProduceBlock b
      | expectedMessage s == Message b (envHost s)
      , b /= lastEnvBlock -> True
    _ -> False

  validFailingAction _ _ = True

  arbitraryAction ctx s =
    frequency
      [ (10, pure $ Some Tick)
      , (10, Some . ProduceBlock <$> nextEnvBlock s)
      , (1, Some . ProduceBlock . Block <$> arbitrary)
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
    ProduceBlock b -> do
      when (expectedMessage s == Message b (envHost s)) $ do
        put b
      onNode $ flip nodeSendTo $ Message b (envHost s)

  postcondition (_, s@EnvState{..}) Tick _ msgs = do
    lastHonestBlock <- lift get
    case msgs of
      []
        | time `mod` 3 == 2
        , messageOriginator (expectedMessage s) == sutHost
        , messageBlock (expectedMessage s) /= lastHonestBlock -> do
            counterexamplePost $ "Node failed to produce a block in time"
            pure False
        | otherwise -> pure True
      [m]
        | messageOriginator m /= sutHost -> do
            counterexamplePost $ "Node produced message with incorrect host " ++ show m
            pure False
        | m /= expectedMessage s -> do
            counterexamplePost $ "Node produced an unexpected message " ++ show m
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
  postcondition _ _ _ _ = pure True

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
  }

type HonestNodeMonad = ReaderT HonestNodeState IO

runHonestMonad :: PropertyM HonestNodeMonad () -> Property
runHonestMonad m = monadicIO $ do
  clock <- lift $ newIORef 0
  block <- lift $ newIORef (-1)
  runPropertyReaderT m $ HonestNodeState clock block

honestNode :: Host -> Node HonestNodeMonad
honestNode h = Node{..}
  where nodeSendTo (Message (Block n) sender) = do
          block <- asks honestNodeLastBlock
          clock <- asks honestNodeClock
          time     <- lift $ readIORef clock
          lastSeen <- lift $ readIORef block
          let validBlock = n == lastSeen + 1 && sender == whoseSlot time
          when validBlock $
            lift $ writeIORef block n
        nodeReceiveFrom = do
          clock <- asks honestNodeClock
          block <- asks honestNodeLastBlock
          time <- lift $ readIORef clock
          n    <- lift $ readIORef block
          let shouldSend = time `mod` 3 == 1 && h == whoseSlot time
          when shouldSend $
            lift $ writeIORef block (n + 1)
          pure [ Message (Block $ n + 1) h | shouldSend ]
        nodeProgressTime = do
          clock <- asks honestNodeClock
          lift $ modifyIORef clock (+1)

