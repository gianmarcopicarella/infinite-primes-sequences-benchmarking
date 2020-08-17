
module Main (main) where

import qualified AutoBench.Internal.Benchmarking
import qualified Input

main :: IO ()
main  = AutoBench.Internal.Benchmarking.runBenchmarks (AutoBench.Internal.Benchmarking.genBenchmarksGenNfUn [("Input.uE", Input.uE), ("Input.eS", Input.eS), ("Input.fES", Input.fES), ("Input.eSH", Input.eSH), ("Input.eSW", Input.eSW), ("Input.eSI", Input.eSI), ("Input.eSPQ", Input.eSPQ), ("Input.eSWPQ", Input.eSWPQ)] Input.ts) Input.ts