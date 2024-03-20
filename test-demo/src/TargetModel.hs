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
-- Network model:
--  - messages diffuse over the network instantly to all other
--    hosts.

-- TODO: the current model doesn't increment the blocks because negative actions
-- (specifically negative `Tick`s!) mean that sometimes the environment (dishonestly)
-- fails to trasmit a message! That means the chain isn't unbroken. However, we don't
-- detect that safety property here because we aren't observing the fact that when the
-- sut sends a message it always sends the message that contains the slot number, not the
-- increment of the last message we received. Something to think about here.

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
      | expectedMessage time == Message b (envHost s)
      , b /= lastEnvBlock -> True
    _ -> False

  validFailingAction _ _ = True

  arbitraryAction ctx s =
    oneof [ pure $ Some Tick
          , Some . ProduceBlock <$> nextEnvBlock s
          , Some . ProduceBlock . Block <$> arbitrary
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
      when (expectedMessage time == Message b (envHost s)) $ do
        put b
      onNode $ flip nodeSendTo $ Message b (envHost s)

  postcondition (_, EnvState{..}) Tick _ msgs = do
    lastHonestBlock <- lift get
    case msgs of
      []
        | time `mod` 3 == 2
        , messageOriginator (expectedMessage time) == sutHost
        , messageBlock (expectedMessage time) /= lastHonestBlock -> do
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
  () <$ runPropertyStateT (runPropertyReaderT (runActions as) node) (Block 0)

-- Honest implementation --------------------------------------------------

prop_honest :: Actions EnvState -> Property
prop_honest = prop_nodeCorrect (honestNode Alice) runHonestMonad

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
