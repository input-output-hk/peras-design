module TargetModel where

import Data.IORef
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

expectedMessage :: Integer -> Message
expectedMessage time
  | even slot = Message (Block slot) Alice
  | otherwise = Message (Block slot) Bob
  where slot = time `div` 3

instance StateModel EnvState where
  data Action EnvState a where
    ProduceBlock :: Block -> Action EnvState ()
    -- ^ The environment produces a block
    Tick :: Action EnvState [Message]
    -- ^ Time progresses by one unit

  initialState = EnvState { lastEnvBlock = Block 0
                          , sutHost      = Alice
                          , time         = 0
                          }

  nextState s (ProduceBlock b) _ = s { lastEnvBlock = b }
  nextState s Tick             _ = s { time = time s + 1 }

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
      | environmentsTurn s
      , isNextEnvBlock s b -> True
    _ -> False

  arbitraryAction ctx s =
    oneof [ pure $ Some Tick
          , Some . ProduceBlock <$> nextEnvBlock s
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
      put b
      onNode $ flip nodeSendTo $ Message b (envHost s)

  postcondition (_, EnvState{..}) Tick _ msgs = do
    lastBlock <- lift get
    case msgs of
      []
        | time `mod` 3 == 2
        , messageOriginator (expectedMessage time) == sutHost
        , messageBlock (expectedMessage time) /= lastBlock -> do
            counterexamplePost $ "Node failed to produce a block in time"
            pure False
        | otherwise -> pure True
      [m]
        | messageOriginator m /= sutHost -> do
            counterexamplePost $ "Node produced message with incorrect host " ++ show m
            pure False
        | m /= expectedMessage time -> do
            counterexamplePost $ "Node produced an unexpected message " ++ show m
            pure False
        | messageBlock m == lastBlock -> do
            counterexamplePost $ "Node produced the same block twice " ++ show m
            pure False
        | otherwise -> do
            lift $ put (messageBlock m)
            pure True
      _ -> do
        counterexamplePost $ "Node produced too many messages " ++ show msgs
        pure False
  postcondition _ _ _ _ = pure True

prop_node_correct :: (Monad m, RunModel EnvState (ModelMonad m))
                  => Node m
                  -> (PropertyM m () -> Property)
                  -> Actions EnvState
                  -> Property
prop_node_correct node runProp as = runProp $ do
  () <$ runPropertyStateT (runPropertyReaderT (runActions as) node) (Block 0)

-- Honest implementation --------------------------------------------------

type HonestNodeMonad = ReaderT (IORef Integer) IO

runHonestMonad :: PropertyM HonestNodeMonad () -> Property
runHonestMonad m = monadicIO $ do
  ref <- lift $ newIORef 0
  runPropertyReaderT m ref

honestNode :: Host -> Node HonestNodeMonad
honestNode h = Node{..}
  where nodeSendTo _ = pure ()
        nodeReceiveFrom = do
          ref <- ask
          time <- lift $ readIORef ref
          let em = expectedMessage time
          pure [ em
               | time `mod` 3 == 1
               , messageOriginator em == h
               , time `div` 3 > 0
               ]
        nodeProgressTime = do
          ref <- ask
          lift $ modifyIORef ref (+1)
