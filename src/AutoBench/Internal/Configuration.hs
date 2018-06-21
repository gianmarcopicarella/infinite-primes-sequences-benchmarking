
{-# OPTIONS_GHC -Wall #-}

-- |
--
-- Module      : AutoBench.Internal.Configuration
-- Description : Configuration file
-- Copyright   : (c) 2018 Martin Handley
-- License     : BSD-style
-- Maintainer  : martin.handley@nottingham.ac.uk
-- Stability   : Experimental
-- Portability : GHC
--
-- This module contains system-wide settings and defaults.
--

-------------------------------------------------------------------------------
-- <TO-DO>:
-------------------------------------------------------------------------------
-- 

module AutoBench.Internal.Configuration 
  (
  -- * User inputs
    minimumTestInputs                -- The minimum number of distinctly sized test inputs required by test suites.
  , unaryTestDataConstructor         -- The data constructor for user-specified test data for unary test programs.
  , binaryTestDataConstructor        -- The data constructor for user-specified test data for binary test programs.
  , testSuiteDataConstructor         -- The data constructor for test suites.
  -- * Benchmarking
  , defaultBenchmarkReportFilepath   -- The default filepath for saving benchmarking data produced by Criterion.
  -- * Statistical analysis 
  , maximumCVIterations              -- The maximum number of cross-validation iterations.
  , maximumCVTrainingData            -- The maximum percentage of data to use for training regression models during cross-validation.
  , maximumModelPredictors           -- The maximum number of predictors for regression models.
  , minimumCVIterations              -- The minimum number of cross-validation iterations.
  , minimumCVTrainingData            -- The minimum percentage of data to use for training regression models during cross-validation.
  -- * Misc 
  , version                          -- The system's version.

  ) where 


-- * User inputs 

-- | The minimum number of distinctly sized test inputs required by test suites.
--
-- > minimumTestInputs = 20
minimumTestInputs :: Int
minimumTestInputs  = 20

-- | The data constructor for user-specified test data for unary test programs.
--
-- > unaryTestDataConstructor  = "UnaryTestData"
unaryTestDataConstructor :: String 
unaryTestDataConstructor  = "UnaryTestData"

-- | The data constructor for user-specified test data for binary test programs.
--
-- > binaryTestDataConstructor  = "BinaryTestData"
binaryTestDataConstructor :: String 
binaryTestDataConstructor  = "BinaryTestData"

-- | The data constructor for test suites.
--
-- > testSuiteDataConstructor  = "TestSuite"
testSuiteDataConstructor :: String 
testSuiteDataConstructor  = "TestSuite"

-- * Benchmarking

-- | The default filepath for saving benchmarking data produced by Criterion. 
-- Note: the report produced by Criterion is in a JSON format.
--
-- > defaultBenchmarkReportFilepath  = "./autobench_tmp.json"
defaultBenchmarkReportFilepath :: FilePath
defaultBenchmarkReportFilepath  = "./autobench_tmp.json"

-- * Statistical analysis

-- | The maximum number of predictors for regression models.
--
-- > maximumModelPredictors = 10
maximumModelPredictors :: Int
maximumModelPredictors  = 10

-- | The minimum percentage of data to use for training regression models during
-- cross-validation.
--
-- > minimumCVTrainingData = 0.5
minimumCVTrainingData :: Double
minimumCVTrainingData  = 0.5

-- | The maximum percentage of data to use for training regression models during
-- cross-validation.
--
-- > maximumCVTrainingData = 0.8
maximumCVTrainingData :: Double 
maximumCVTrainingData  = 0.8

-- | The minimum number of cross-validation iterations.
--
-- > minimumCVIterations = 100
minimumCVIterations :: Int 
minimumCVIterations  = 100

-- | The maximum number of cross-validation iterations.
--
-- > maximumCVIterations = 500
maximumCVIterations :: Int 
maximumCVIterations  = 500

-- * Misc 

-- | The system's version.
--
-- > version  = "AutoBench (Version 0.1.0.0)"
version :: String 
version  = "AutoBench (Version 0.1.0.0)"