{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Main (
  main,
) where

import NumericPrelude.Base
import NumericPrelude.Numeric hiding (sum)

import Control.Applicative (pure, (<$>), (<*>))
import Control.Monad (unless, when)
import Data.Default (def)
import Data.Foldable (sum, toList)
import Data.Function (on)
import Data.List (intercalate)
import Data.Maybe (fromMaybe)
import Data.Monoid ((<>))
import Data.Time (getCurrentTime)
import Data.Time.Clock (diffUTCTime)
import Data.Version (showVersion)
import Data.Yaml (decodeFileThrow)
import Paths_peras_markov (version)
import Peras.Markov.Adversary (transitions)
import Peras.Markov.Orphans ()
import Peras.Markov.Polynomial (evaluate)
import Prettyprinter (Pretty (pretty), fill, (<+>))
import System.IO (
  IOMode (WriteMode),
  hClose,
  hFlush,
  hPutStr,
  hPutStrLn,
  openFile,
  stderr,
 )

import qualified Data.Map.Strict as Map
import qualified Options.Applicative as O
import qualified Peras.Markov.Adversary.CommonCandidate as CommonCandidate
import qualified Peras.Markov.Adversary.TwoChain as TwoChain (lookupDelta, separatedChains, splitChains)
import qualified Peras.Markov.Polynomial as Var (p, q)
import qualified Peras.MarkovSim.Transition as MarkovSim
import qualified Peras.MarkovSim.Types as MarkovSim

main :: IO ()
main = run =<< O.execParser scenarioParser

data Scenario
  = EverLonger
      { ε :: Double
      , slots :: Int
      , stake :: (Int, Int)
      , paramFile :: FilePath
      , behaviorFile :: FilePath
      , outFile :: FilePath
      , progress :: Bool
      }
  | LongerChain
      { ε :: Double
      , slots :: Int
      , stake :: (Int, Int)
      , paramFile :: FilePath
      , behaviorFile :: FilePath
      , outFile :: FilePath
      , stop :: Double
      , progress :: Bool
      }
  | MarginReach
      { ε :: Double
      , slots :: Int
      , stake :: (Int, Int)
      , paramFile :: FilePath
      , behaviorFile :: FilePath
      , outFile :: FilePath
      , progress :: Bool
      }
  | LengthDifference
      { ε :: Double
      , slots :: Int
      , stake :: (Int, Int)
      , paramFile :: FilePath
      , behaviorFile :: FilePath
      , outFile :: FilePath
      , progress :: Bool
      }
  | Lengths
      { ε :: Double
      , slots :: Int
      , stake :: (Int, Int)
      , paramFile :: FilePath
      , behaviorFile :: FilePath
      }
  | CommonCandidateDemo
  | SeparateChainsDemo
  deriving (Eq, Ord, Read, Show)

run :: Scenario -> IO ()
run EverLonger{..} =
  do
    peras <- decodeFileThrow paramFile
    behavior <- decodeFileThrow behaviorFile
    hout <- openFile outFile WriteMode
    hPutStrLn hout $
      intercalate
        "\t"
        [ "Slot"
        , "P(adversary >= honest | θ = " <> show (case MarkovSim.thresholding behavior of MarkovSim.NoThresholding -> 0; MarkovSim.MkThreshold t -> t) <> ")"
        ]
    let probabilities = uncurry (MarkovSim.mkProbabilities peras) stake
        initial = MarkovSim.behavioralEvolution behavior
        go i prior
          | i > slots = return ()
          | otherwise =
              do
                let posterior = MarkovSim.pstep ε peras probabilities prior
                    summary =
                      Map.mapKeysWith (+) MarkovSim.adversaryEverLonger $
                        MarkovSim.getEvolution posterior
                hPutStrLn hout $ intercalate "\t" [show i, show $ fromMaybe 0 $ Map.lookup True summary]
                when progress . hPutStr stderr $ "\rSlot: " <> show i <> "  Size: " <> show (Map.size $ MarkovSim.getEvolution posterior) <> "  Surprise: " <> take 10 (maybe "∞" (show . negate . logBase 2) (Map.lookup True summary) <> replicate 20 ' ')
                hFlush hout
                go (i + 1) posterior
    when progress $
      hPutStrLn stderr ""
    go (1 :: Int) initial
    hClose hout
    when progress $
      hPutStrLn stderr $
        replicate 80 ' '
run LongerChain{..} =
  do
    peras <- decodeFileThrow paramFile
    behavior <- decodeFileThrow behaviorFile
    hout <- openFile outFile WriteMode
    hPutStrLn hout $ intercalate "\t" ["Slot", "P(honest > adversary)", "P(adversary >= honest)", "Error bound"]
    let probabilities = uncurry (MarkovSim.mkProbabilities peras) stake
        initial = MarkovSim.behavioralEvolution behavior
        go i prior
          | i > slots = return ()
          | otherwise =
              do
                let posterior = MarkovSim.pstep ε peras probabilities prior
                    summary =
                      Map.mapKeysWith (+) (\MarkovSim.MkChains{MarkovSim.honest, MarkovSim.adversary} -> on (>) MarkovSim.weight honest adversary) $
                        MarkovSim.getEvolution posterior
                hPutStrLn hout $ intercalate "\t" [show i, show $ fromMaybe 0 $ Map.lookup True summary, show $ fromMaybe 0 $ Map.lookup False summary, show . abs $ 1 - sum summary]
                when progress . hPutStr stderr $ "\rSlot: " <> show i <> "  Size: " <> show (Map.size $ MarkovSim.getEvolution posterior) <> "  Surprise: " <> take 10 (maybe "∞" (show . negate . logBase 2) (Map.lookup False summary) <> replicate 20 ' ')
                hFlush hout
                unless (maybe True (< stop) $ Map.lookup False summary) $
                  go (i + 1) posterior
    when progress $
      hPutStrLn stderr ""
    go (1 :: Int) initial
    hClose hout
    when progress $
      hPutStrLn stderr $
        replicate 80 ' '
run MarginReach{..} =
  do
    peras <- decodeFileThrow paramFile
    behavior <- decodeFileThrow behaviorFile
    hout <- openFile outFile WriteMode
    hPutStrLn hout $ intercalate "\t" ["Slot", "Margin", "Reach", "Probability"]
    let probabilities = uncurry (MarkovSim.mkProbabilities peras) stake
        initial = MarkovSim.behavioralEvolution behavior
        go i prior
          | i > slots = return ()
          | otherwise =
              do
                let posterior = MarkovSim.pstep ε peras probabilities prior
                    summary =
                      Map.toList
                        . Map.mapKeysWith (+) MarkovSim.computeMarginReach
                        $ MarkovSim.getEvolution posterior
                hPutStr hout $ unlines $ (\(k, v) -> intercalate "\t" [show i, show $ fst k, show $ snd k, show v]) <$> summary
                when progress . hPutStr stderr $ "\rSlot: " <> show i <> "  Size: " <> take 15 (show (Map.size $ MarkovSim.getEvolution posterior) <> replicate 15 ' ')
                hFlush hout
                go (i + 1) posterior
    when progress $
      hPutStrLn stderr ""
    go (1 :: Int) initial
    hClose hout
    when progress $
      hPutStrLn stderr "                       "
run LengthDifference{..} =
  do
    peras <- decodeFileThrow paramFile
    behavior <- decodeFileThrow behaviorFile
    hout <- openFile outFile WriteMode
    hPutStrLn hout $ intercalate "\t" ["Slot", "Honest - Adversary", "Probability"]
    let probabilities = uncurry (MarkovSim.mkProbabilities peras) stake
        initial = MarkovSim.behavioralEvolution behavior
        go i prior
          | i > slots = return ()
          | otherwise =
              do
                let posterior = MarkovSim.pstep ε peras probabilities prior
                    summary =
                      Map.toList
                        . Map.mapKeysWith (+) (\MarkovSim.MkChains{MarkovSim.honest, MarkovSim.adversary} -> on (-) MarkovSim.weight honest adversary)
                        $ MarkovSim.getEvolution posterior
                hPutStr hout $ unlines $ (\(k, v) -> intercalate "\t" [show i, show k, show v]) <$> summary
                when progress . hPutStr stderr $ "\rSlot: " <> show i <> "  Size: " <> take 15 (show (Map.size $ MarkovSim.getEvolution posterior) <> replicate 15 ' ')
                hFlush hout
                go (i + 1) posterior
    when progress $
      hPutStrLn stderr ""
    go (1 :: Int) initial
    hClose hout
    when progress $
      hPutStrLn stderr "                       "
run Lengths{..} =
  do
    peras <- decodeFileThrow paramFile
    behavior <- decodeFileThrow behaviorFile
    let probabilities = uncurry (MarkovSim.mkProbabilities peras) stake
        initial = MarkovSim.behavioralEvolution behavior
        metrics f =
          do
            t0 <- getCurrentTime
            let MarkovSim.MkEvolution{MarkovSim.getEvolution} = f ε peras probabilities slots initial
            putStrLn $ "Size: " <> show (Map.size getEvolution)
            putStrLn $ "Entropy: " <> show (sum $ (\p -> -p * logBase 2 p) <$> toList getEvolution)
            putStrLn $ "Total probability: " <> show (sum getEvolution)
            putStrLn $ "Honest length: " <> show (sum $ (\(chains, probability) -> probability * fromIntegral (MarkovSim.weight $ MarkovSim.honest chains)) <$> Map.toList getEvolution)
            putStrLn $ "Adversary length: " <> show (sum $ (\(chains, probability) -> probability * fromIntegral (MarkovSim.weight $ MarkovSim.adversary chains)) <$> Map.toList getEvolution)
            t1 <- getCurrentTime
            putStrLn $ "Elapsed time: " <> show (t1 `diffUTCTime` t0)
    putStrLn ""
    {-
      putStrLn "Serial"
      metrics MarkovSim.steps
      putStrLn ""
      putStrLn "Parallel"
    -}
    metrics MarkovSim.psteps
    putStrLn ""
run CommonCandidateDemo{} =
  do
    let perasU = 150
        perasL = 60
        p = 0.75 / 20 :: Double
        q = 0.25 / 20
        (result, noBlock) = CommonCandidate.scenario perasU perasL p q
    print' ""
    print $ CommonCandidate.summarize result
    print $ fill 30 (pretty "No adversary candidate") <+> pretty noBlock
run SeparateChainsDemo{} =
  do
    print' ""
    print' "# Symbolic and numeric computation of adversarial scenarios."
    print' ""
    print' ""

    let result = transitions Var.p Var.q 10 TwoChain.separatedChains def
    print' "## Adversary builds a chain separately from the honest parties."
    print' ""
    print' "In this example the delta is the length of the honest chain minus the length"
    print' "of the adversarial chain. We generate ten blocks."
    print' ""
    print' result

    let p = 2 % 3 :: Rational
        q = 1 % 3
        result' = evaluate p q result
    print' ""
    print $ pretty "Now substitute p =" <+> pretty p <+> pretty "and q =" <+> pretty q <+> pretty "into the result."
    print' ""
    print' result'

    let p' = 2 / 3 :: Double
        q' = 1 / 3
        result'' = transitions p' q' 10 TwoChain.splitChains def
    print' ""
    print' ""
    print' "## Adversary lengthens whichever of two chains is shorter."
    print' ""
    print' "In this example the delta is the difference in length between the two chains."
    print' "Here we bypass the symbolic computation and use double-precision floating-"
    print' "point numbers. We generate ten blocks."
    print' ""
    print' result''

    let n = 2160
        result''' = transitions p' q' n TwoChain.splitChains def
    print' ""
    print $ pretty "Repeat the computation for" <+> pretty n <+> pretty "blocks and just print the result for when"
    print' "delta is zero."
    print' ""
    Just answer <- return $ 0 `TwoChain.lookupDelta` result'''
    print answer

    print' ""
    print' "We can sum all of the probabilities to check that they equal one and that"
    print' "round-off errors are not a problem."
    print' ""
    print $ sum result'''

print' :: Pretty a => a -> IO ()
print' = print . pretty

scenarioParser :: O.ParserInfo Scenario
scenarioParser =
  let
    εOption = O.option O.auto $ O.long "epsilon" <> O.value 1e-30 <> O.showDefault <> O.metavar "DOUBLE" <> O.help "Threshhold for discarding small probabilities."
    slotOption = O.option O.auto $ O.long "slots" <> O.value 1000 <> O.showDefault <> O.metavar "NATURAL" <> O.help "Number of slots to simulate."
    stakeOption = fmap (\x -> (1_000_000_000 - round (1_000_000_000 * x :: Double), round (1_000_000_000 * x))) . O.option O.auto $ O.long "adversarial-stake" <> O.value 0.05 <> O.showDefault <> O.metavar "FRACTION" <> O.help "Fraction [%/100] of adversarial stake."
    paramOption = O.strOption $ O.long "param-file" <> O.metavar "FILE" <> O.help "Path to input YAML file containing the Peras protocol parameters."
    outOption = O.strOption $ O.long "out-file" <> O.value "/dev/stdout" <> O.showDefault <> O.metavar "FILE" <> O.help "Path to output TSV file containing the simulation results."
    stopOption = O.option O.auto $ O.long "stop" <> O.value 0 <> O.showDefault <> O.metavar "DOUBLE" <> O.help "Stop simulation when probabilities are smaller than this value."
    behaviorOption = O.strOption $ O.long "behavior-file" <> O.metavar "FILE" <> O.help "Path to input YAML file containing the adversarial behaviors."
    progressOption = O.switch $ O.long "progress" <> O.help "Show the progress of the simulation."
    postFactoCommand =
      O.command "ever-longer" $
        O.info (EverLonger <$> εOption <*> slotOption <*> stakeOption <*> paramOption <*> behaviorOption <*> outOption <*> progressOption) $
          O.progDesc "Compute the probability of a private adversarial chain being longer than the honest one."
    longerChainCommand =
      O.command "longer-chain" $
        O.info (LongerChain <$> εOption <*> slotOption <*> stakeOption <*> paramOption <*> behaviorOption <*> outOption <*> stopOption <*> progressOption) $
          O.progDesc "Compute the probability of a private adversarial chain being longer than the honest one."
    marginReachCommand =
      O.command "margin-reach" $
        O.info (MarginReach <$> εOption <*> slotOption <*> stakeOption <*> paramOption <*> behaviorOption <*> outOption <*> progressOption) $
          O.progDesc "Compute the probability distribution of the margin and reach for a one-slot diffusion time."
    lengthDifferenceCommand =
      O.command "length-difference" $
        O.info (LengthDifference <$> εOption <*> slotOption <*> stakeOption <*> paramOption <*> behaviorOption <*> outOption <*> progressOption) $
          O.progDesc "Compute the probability distribution of the length of the honest chain minus the length of the adversarial chain."
    lengthsCommand =
      O.command "lengths" $
        O.info (Lengths <$> εOption <*> slotOption <*> stakeOption <*> paramOption <*> behaviorOption) $
          O.progDesc "Compute the mean lengths of the honest and adversarial chains."
    commonCandidateDemoCommand =
      O.command "common-candidate-demo" $
        O.info (pure CommonCandidateDemo) $
          O.progDesc "Demonstrate a common-candidate simulation."
    separateChainsDemoCommand =
      O.command "separate-chains-demo" $
        O.info (pure SeparateChainsDemo) $
          O.progDesc "Demonstrate a separate-chain simulation."
   in
    O.info
      ( O.helper
          <*> O.infoOption ("peras-markov " <> showVersion version) (O.long "version" <> O.help "Show version.")
          <*> O.hsubparser (postFactoCommand <> longerChainCommand <> marginReachCommand <> lengthDifferenceCommand <> lengthsCommand <> commonCandidateDemoCommand <> separateChainsDemoCommand)
      )
      ( O.fullDesc
          <> O.progDesc "This command-line tool runs Markov-chain simulations of the Peras protocol."
          <> O.header "peras-markov: simulate Peras protocol using Markov chains"
      )
