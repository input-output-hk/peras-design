module TestModelQC where

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
import TestModel

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
      , (5, Some . Step . DishonestProduceBlock . Blk <$> arbitrary)
      , (5, pure $ Some $ Step DishonestTick)
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
    DishonestTick -> do
      msgs <- onNode nodeReceiveFrom
      onNode nodeProgressTime
      pure msgs
    ProduceBlock b -> do
      onNode $ \ sut -> nodeSendTo sut (envParty s) b
      pure []
    DishonestProduceBlock b -> do
      onNode $ \ sut -> nodeSendTo sut (envParty s) b
      pure []

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

