module Input where 

import Data.PQueue.Prio.Min (empty, insert, findMin, deleteMin)

import Data.Default (def)
import AutoBench.QuickCheck
import AutoBench.Types
import Test.QuickCheck (Arbitrary(..), sized)
import Control.DeepSeq (NFData(..))



-- Wheel structure
w0 = [1]
nextWheel [] _ _ = w0
nextWheel (w:ws) p np = nWAux (rep p (ws++[w])) np p where
  nWAux [] _ _ = []
  nWAux [w] _ _ = [w]
  nWAux (w:ws) s p 
    | mod (w+s) p == 0 = nWAux ((w+head ws):(tail ws)) s p
    | otherwise = w:nWAux ws (w+s) p
  rep 0 _ = []
  rep n xs = xs ++ rep (n-1) xs
nextWheel1 ws@(w:_) p = nextWheel ws p (p+w)
circ w = w ++ circ w
spin (w:ws) n = n:spin ws (n+w)


genWheel :: [Int] -> [Int]
genWheel [2] = [2]
genWheel xs
  | length cpl == 0 = []
  | otherwise = go (head cpl) (tail cpl) where
    c = foldr (*) 1 xs
    cpl = [x | x <- [2..(c+1)], cp x]
    cp x = foldr (&&) True [mod x p /= 0 | p <- xs]
    go a (b:t) = (b - a) : go b t
    go a [] = [(head cpl + c) - a]


-- minus and union procedures
minus xs@(x:txs) ys@(y:tys)
  | x < y = x : minus txs ys
  | x > y = minus xs tys
  | otherwise = minus txs tys

union xs@(x:txs) ys@(y:tys)
  | x == y = x:union txs tys
  | x < y = x:union txs ys
  | x > y = y:union xs tys

sMinus xs@(x:txs) ys@(y:tys)
  | x==y = sMinus txs tys
  | otherwise = x:sMinus txs ys

dUnion xs@(x:txs) ys@(y:tys)
  | x < y = x:dUnion txs ys
  | otherwise = y:dUnion xs tys
dUnion xs [] = xs

-- Trial division
trialDiv :: PositiveInt -> Int
trialDiv (PositiveInt x) = primes !! x where
  primes = 2 : [i | i <- [3..],  
    and [rem i p > 0 | p <- takeWhile (\p -> p^2 <= i) primes]]


-- Turner
turner :: PositiveInt -> Int
turner (PositiveInt x) = (filterPrime [2..]) !! x where
  filterPrime (p:xs) =
    p : filterPrime [x | x <- xs, (mod x p) /= 0]

-- Euler's sieve naive
eulerNaive :: PositiveInt -> Int
eulerNaive (PositiveInt x) = (eulerSieve [2..]) !! x where
  eulerSieve cs@(p:tcs) = p:eulerSieve (minus tcs (map (p*) cs))

---------------------------------------------------------------------------------------------

-- Bird-Eratostene
birdEra :: PositiveInt -> Int
birdEra (PositiveInt x) = primes !! x where
  primes = 2:([3..] `minus` composites)
  composites = foldr unionP [] [multiples p | p <- primes]
  multiples n = map (n*) [n..]
  unionP (x:xs) ys = x:union xs ys



-- Bird-Salvo
eulerHamming :: PositiveInt -> Int
eulerHamming (PositiveInt x) = primes !! x where
  composites (x:xs) = cmpsts where
    cmpsts = (x*x):map (x*) (dUnion xs cmpsts) `dUnion` (composites xs)
  primes = 2:([3..] `sMinus` composites primes)


-- Euler's sieve inductive sets
birdSalvo :: PositiveInt -> Int
birdSalvo (PositiveInt x) = primes !! x where
  primes = 2:([3..] `sMinus` (composites primes [2..]))
  composites (p:ps) ss@(s:tss) = es `dUnionP` composites ps ss' where
    es = map (p*) ss
    ss' = tss `sMinus` es
    dUnionP (x:xs) ys = x : dUnion xs ys

------------------------------------------------------------------------------------------------




-- Euler's sieve with priority queue (avoiding stream fusion)
oNeillPQ :: PositiveInt -> Int
oNeillPQ (PositiveInt x) = (sieve [2..]) !! x where
  sieve (c:cs) = c:sieve' cs ss (insert (c*c) (tail es) empty) where 
      es = map (c*) (c:cs)
      ss = cs `sMinus` es
      sieve' cs@(c:tcs) ss tbl
        | c < n = c : sieve' tcs ss' tbl'
        | otherwise = sieve' tcs ss tbl'' where 
          (n, m:ms) = findMin tbl
          es = map (c*) ss
          ss' = tail (ss `sMinus` es)
          tbl' = insert (c*c) (tail es) tbl
          tbl'' = insert m ms (deleteMin tbl)



-- Euler's sieve with priority queue and wheel (avoiding stream fusion)
oNeillWPQ :: PositiveInt -> Int
oNeillWPQ (PositiveInt x) = primes !! x where
  sieve (c:cs) w = c:sieve' cs (nextWheel1 w c)
    (insert (c*c) (circ (map (c*) w)) empty) where 
      sieve' cs@(c:tcs) w tbl
        | c < n = c : sieve' tcs w' tbl'
        | otherwise = sieve' tcs w tbl'' where 
          (n, m:ms) = findMin tbl
          w' = nextWheel1 w c
          tbl' = insert (c*c) (circ (map (c*) w)) tbl
          tbl'' = insert (n+m) ms (deleteMin tbl)
  primes = sieve (spin (circ w0) 2) w0




-- Euler's sieve from Hamming sequence equipped with a 4 primes wheel
eulerHammingW4 :: PositiveInt -> Int
eulerHammingW4 (PositiveInt x) = primes !! x where
  composites (x:xs) = cmpsts where
    cmpsts = (x*x):map (x*) (dUnion xs cmpsts) `dUnion` (composites xs)
  primes = 2:3:5:7:11:t4 `sMinus` composites (drop 4 primes) where
    w4 = nextWheel1 [4,2,4,2,4,6,2,6] 7
    s4 = spin (circ w4) 11
    t4 = tail s4

-- Euler's sieve inductive sets equipped with a 4 primes wheel
birdSalvoW4 :: PositiveInt -> Int
birdSalvoW4 (PositiveInt x) = primes !! x where
  primes = 2:3:5:7:11:t4 `sMinus` (composites (drop 4 primes) s4) where
    w4 = nextWheel1 [4,2,4,2,4,6,2,6] 7
    s4 = spin (circ w4) 11
    t4 = tail s4
  composites (p:ps) ss@(s:tss) = es `dUnionP` composites ps ss' where
    es = map (p*) ss
    ss' = tss `sMinus` es
    dUnionP (x:xs) ys = x : dUnion xs ys

oNeillWPQ4 :: PositiveInt -> Int
oNeillWPQ4 (PositiveInt x) = primes !! x where
  sieve (c:cs) w = c:sieve' cs (nextWheel1 w c)
    (insert (c*c) (circ (map (c*) w)) empty) where 
      sieve' cs@(c:tcs) w tbl
        | c < n = c : sieve' tcs w' tbl'
        | otherwise = sieve' tcs w tbl'' where 
          (n, m:ms) = findMin tbl
          w' = nextWheel1 w c
          tbl' = insert (c*c) (circ (map (c*) w)) tbl
          tbl'' = insert (n+m) ms (deleteMin tbl)
  primes = 2:3:5:7:sieve s4 w4 where
    w4 = nextWheel1 [4,2,4,2,4,6,2,6] 7
    s4 = spin (circ w4) 11

oNeillPQ4 :: PositiveInt -> Int
oNeillPQ4 (PositiveInt x) = (2:3:5:7:(sieve s4)) !! x where
  w4 = nextWheel1 [4,2,4,2,4,6,2,6] 7
  s4 = spin (circ w4) 11
  sieve (c:cs) = c:sieve' cs ss (insert (c*c) (tail es) empty) where 
      es = map (c*) (c:cs)
      ss = cs `sMinus` es
      sieve' cs@(c:tcs) ss tbl
        | c < n = c : sieve' tcs ss' tbl'
        | otherwise = sieve' tcs ss tbl'' where 
          (n, m:ms) = findMin tbl
          es = map (c*) ss
          ss' = tail (ss `sMinus` es)
          tbl' = insert (c*c) (tail es) tbl
          tbl'' = insert m ms (deleteMin tbl)

-- Bird-Picarella w4
birdPicarellaW4 :: PositiveInt -> Int
birdPicarellaW4 (PositiveInt x) = primes !! x where
  primes = 2:3:5:7:11:13:(drop 2 ss) `sMinus` comp
  unionP (x:xs) ys = x:dUnion xs ys
  comp = foldr unionP [] (mult (drop 5 primes) w4)
  mult (p:xs) w = (map (p*) s) : mult xs nw where
    s  = spin (circ w) p
    nw = nextWheel1 w p
  w4 = genWheel [2,3,5,7]
  ss = spin (circ w4) 11
  
------------------------------------------------------------------------------------------------

newtype PositiveInt = PositiveInt Int deriving Show

instance Arbitrary PositiveInt where
  arbitrary = sized(\n -> 
    if n < 0 
    then error $ "valore negativo" ++ show n
    else return $ PositiveInt n)

instance NFData PositiveInt where 
  rnf (PositiveInt n) = rnf n


ts_AVANZATI_TRY :: TestSuite
ts_AVANZATI_TRY = def {
  _dataOpts = Gen 0 500000 10000000,
  _progs = ["birdEraW4"],
  _analOpts = def {
    _graphFP   = Just "./Benchmarks/AutoBenched_AVANZATI_TRY.png",
    _reportFP  = Just "./Benchmarks/AutoBenchPerformance_AVANZATI_TRY.txt",                         
    _coordsFP  = Just "./Benchmarks/AutoBenched_AVANZATI_TRY.csv"
  }
}


ts_ELEMENTARI :: TestSuite
ts_ELEMENTARI = def {
  _dataOpts = Gen 0 1000 20000,
  _progs = ["trialDiv", "turner", "eulerNaive"],
  _analOpts = def {
    _graphFP   = Just "./Benchmarks/AutoBenched_ELEMENTARI.png",
    _reportFP  = Just "./Benchmarks/AutoBenchPerformance_ELEMENTARI.txt",                         
    _coordsFP  = Just "./Benchmarks/AutoBenched_ELEMENTARI.csv"
  }
}

ts_AVANZATI :: TestSuite
ts_AVANZATI = def {
  _dataOpts = Gen 0 70000 1400000,
  _progs = ["birdEra", "birdSalvo", "eulerHamming"],
  _analOpts = def {
    _graphFP   = Just "./Benchmarks/AutoBenched_AVANZATI.png",
    _reportFP  = Just "./Benchmarks/AutoBenchPerformance_AVANZATI.txt",                         
    _coordsFP  = Just "./Benchmarks/AutoBenched_AVANZATI.csv"
  }
}

ts_OTTIMIZZATI :: TestSuite
ts_OTTIMIZZATI = def {
  _dataOpts = Gen 0 70000 1400000,
  _progs = ["oNeillPQ", "oNeillWPQ", "birdSalvoW4", "eulerHammingW4", "oNeillWPQ4", "oNeillPQ4"],
  _analOpts = def {
    _graphFP   = Just "./Benchmarks/AutoBenched_OTTIMIZZATI.png",
    _reportFP  = Just "./Benchmarks/AutoBenchPerformance_OTTIMIZZATI.txt",                         
    _coordsFP  = Just "./Benchmarks/AutoBenched_OTTIMIZZATI.csv"
  }
}

ts_HARD :: TestSuite
ts_HARD = def {
  _dataOpts = Gen 0 228000 4560000,
  _progs = ["oNeillPQ", "oNeillWPQ", "birdSalvoW4", "oNeillWPQ4", "oNeillPQ4", "birdEraW4"],
  _analOpts = def {
    _graphFP   = Just "./Benchmarks/AutoBenched_HARD.png",
    _reportFP  = Just "./Benchmarks/AutoBenchPerformance_HARD.txt",                         
    _coordsFP  = Just "./Benchmarks/AutoBenched_HARD.csv"
  }
}

ts_HARD_2 :: TestSuite
ts_HARD_2 = def {
  _dataOpts = Gen 0 500000 10000000,
  _progs = ["oNeillWPQ", "birdSalvoW4", "oNeillWPQ4", "oNeillPQ4", "birdEraW4"],
  _analOpts = def {
    _graphFP   = Just "./Benchmarks/AutoBenched_HARD_2.png",
    _reportFP  = Just "./Benchmarks/AutoBenchPerformance_HARD_2.txt",                         
    _coordsFP  = Just "./Benchmarks/AutoBenched_HARD_2.csv"
  }
}
