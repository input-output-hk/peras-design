{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

import Control.Concurrent.Class.MonadSTM (
  MonadSTM (atomically, modifyTVar'),
 )
import Control.Monad (void, when)
import Control.Monad.IO.Class (MonadIO (..))
import Control.Tracer (Tracer, nullTracer)
import qualified Data.Aeson as A
import qualified Data.ByteString.Char8 as BS8
import qualified Data.ByteString.Lazy as LBS
import qualified Data.ByteString.Lazy.Char8 as LBS8
import Data.Default (def)
import qualified Data.Map as Map (fromList)
import qualified Data.Set as Set (fromList)
import Data.Version (showVersion)
import qualified Options.Applicative as O
import Paths_peras_simulation (version)
import Peras.Block (Party (pid))
import Peras.Conformance.Params (PerasParams (perasΔ))
import Peras.Conformance.Test.External (NodeRequest (..), NodeResponse (..))
import Peras.Prototype.BlockCreation (blockCreation)
import Peras.Prototype.BlockSelection (selectBlock)
import Peras.Prototype.Crypto (mkCommitteeMember, mkParty, mkSlotLeader)
import Peras.Prototype.Diffusion (diffuseChain, diffuseVote, popChainsAndVotes)
import Peras.Prototype.Fetching (fetching)
import Peras.Prototype.Node (
  NodeState (..),
  defaultNodeState,
  initialNodeState,
  tickNode,
 )
import Peras.Prototype.Trace (PerasLog, perasTracer)
import Peras.Prototype.Types (
  PerasState (certs, chains, votes),
  inRound,
  newRound,
 )
import Peras.Prototype.Voting (voting)
import System.Exit (die)
import System.IO
import Prelude hiding (getLine, round)

main :: IO ()
main =
  do
    Command{..} <- O.execParser commandParser
    {-
        hReader <- openFile simin ReadMode
        hWriter <- openFile simout AppendMode
    -}
    let hReader = stdin
        hWriter = stdout
    hSetBuffering hReader LineBuffering
    hSetBuffering hWriter LineBuffering
    let
      go node =
        do
          -- Verified that this reads UTF-8.
          (A.eitherDecode . LBS.fromStrict <$> BS8.hGetLine hReader)
            >>= \case
              Right req -> do
                (res, node') <- handle (if verbose then perasTracer else nullTracer) node req
                when verbose $ do
                  LBS8.hPutStrLn stderr $ A.encode req
                  LBS8.hPutStrLn stderr $ A.encode res
                  LBS8.hPutStrLn stderr mempty
                case res of
                  Stopped -> pure ()
                  Failed e -> die e
                  _ -> do
                    -- Verified that this writes UTF-8.
                    LBS8.hPutStrLn hWriter $ A.encode res
                    go node'
              Left e -> die $ show e
     in
      go =<< defaultNodeState

handle :: MonadIO m => MonadSTM m => Tracer m PerasLog -> NodeState m -> NodeRequest -> m (NodeResponse, NodeState m)
handle tracer node@MkNodeState{..} =
  \case
    Initialize{..} -> do
      node' <- initialNodeState tracer party slotNumber parameters
      atomically . modifyTVar' stateVar $
        \state ->
          state
            { chains = Set.fromList chainsSeen
            , votes = Set.fromList votesSeen
            , certs = Map.fromList $ (,slotNumber) <$> certsSeen
            }
      pure
        ( def
        , node'
        )
    Tick ->
      pure (def, node{clock = clock + 1})
    Fetching{..} ->
      fetching tracer protocol self stateVar clock newChains newVotes
        >>= \case
          Right () -> pure (def, node)
          Left e -> pure (Failed $ show e, node)
    BlockCreation{..} -> do
      void $ popChainsAndVotes diffuserVar (clock + fromIntegral (perasΔ protocol) + 1)
      let party = mkSlotLeader self clock isSlotLeader
      blockCreation tracer protocol party stateVar clock mempty (diffuseChain diffuserVar)
        >>= \case
          Right () -> (,node) . uncurry NodeResponse <$> popChainsAndVotes diffuserVar (clock + fromIntegral (perasΔ protocol) + 1)
          Left e -> pure (Failed $ show e, node)
    Voting{..} -> do
      void $ popChainsAndVotes diffuserVar (clock + fromIntegral (perasΔ protocol) + 1)
      let party = mkCommitteeMember self protocol clock isCommitteeMember
      voting tracer protocol party stateVar clock (selectBlock tracer) (diffuseVote diffuserVar)
        >>= \case
          Right () -> (,node) . uncurry NodeResponse <$> popChainsAndVotes diffuserVar (clock + fromIntegral (perasΔ protocol) + 1)
          Left e -> pure (Failed $ show e, node)
    NewSlot{..} -> do
      let clock' = clock + 1
          party =
            mkParty
              (pid self)
              (if isSlotLeader then pure clock' else mempty)
              (if isCommitteeMember && newRound clock' protocol then pure $ inRound clock' protocol else mempty)
      void $ popChainsAndVotes diffuserVar (clock' + fromIntegral (perasΔ protocol) + 1)
      tickNode tracer diffuserVar protocol party stateVar clock' (inRound clock' protocol) mempty newChains newVotes
        >>= \case
          Right () -> (,node{clock = clock'}) . uncurry NodeResponse <$> popChainsAndVotes diffuserVar (clock' + fromIntegral (perasΔ protocol) + 1)
          Left e -> pure (Failed $ show e, node{clock = clock'})
    Stop -> pure (Stopped, node)

newtype Command = Command
  { verbose :: Bool
  {-
    , simin :: FilePath
    , simout :: FilePath
  -}
  }
  deriving (Eq, Ord, Read, Show)

commandParser :: O.ParserInfo Command
commandParser =
  let commandOptions =
        {-
                Command
                  <$> O.flag False True (O.long "verbose" <> O.help "Whether to output requests, traces, and responses.")
                  <*> O.strArgument (O.metavar "SIM_IN" <> O.help "Path to the input JSON file or pipe.")
                  <*> O.strArgument (O.metavar "SIM_OUT" <> O.help "Path to the output JSON file or pipe.")
        -}
        Command
          <$> O.flag False True (O.long "verbose" <> O.help "Whether to output requests, traces, and responses.")
   in O.info
        ( O.helper
            <*> O.infoOption ("peras-simulation-pipe " <> showVersion version) (O.long "version" <> O.help "Show version.")
            <*> commandOptions
        )
        ( O.fullDesc
            <> O.progDesc "This command-line tool simulates a Peras node, reading JSON input and writing JSON output."
            <> O.header "peras-simulation-pipe: simulate a Peras node via pipes"
        )
