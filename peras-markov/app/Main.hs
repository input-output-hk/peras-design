{-# LANGUAGE NoImplicitPrelude #-}

module Main (
  main,
  main1,
  main2,
) where

import NumericPrelude.Base
import NumericPrelude.Numeric hiding (sum)

import Data.Default (def)
import Data.Foldable (sum)
import Peras.Markov.Adversary (transitions)
import Peras.Markov.Orphans ()
import Peras.Markov.Polynomial (evaluate)
import Prettyprinter (Pretty (pretty), fill, (<+>))

import qualified Peras.Markov.Adversary.CommonCandidate as CommonCandidate
import qualified Peras.Markov.Adversary.TwoChain as TwoChain (lookupDelta, separatedChains, splitChains)
import qualified Peras.Markov.Polynomial as Var (p, q)

main :: IO ()
main = main2

main2 :: IO ()
main2 =
  do
    let perasU = 150
        perasL = 60
        p = 0.75 / 20 :: Double
        q = 0.25 / 20
        (result, noBlock) = CommonCandidate.scenario perasU perasL p q
    print' ""
    print $ CommonCandidate.summarize result
    print $ fill 30 (pretty "No adversary candidate") <+> pretty noBlock

main1 :: IO ()
main1 =
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