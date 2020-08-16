module Input where 

import Data.PQueue.Prio.Min (empty, insert, findMin, deleteMin)
import Data.Default (def)
import AutoBench.QuickCheck
import AutoBench.Types


uE :: Int -> Int
uE x = (filterPrime [2..]) !! x where
  filterPrime (p:xs) =
    p : filterPrime [x | x <- xs, (mod x p) /= 0]

minus xs@(x:txs) ys@(y:tys)
  | x < y = x : minus txs ys
  | x > y = minus xs txs
  | otherwise = minus txs tys

eS :: Int -> Int
eS x = (eulerSieve [2..]) !! x where
  eulerSieve cs@(p:tcs) = p:eulerSieve (minus tcs (map (p*) cs))


union xs@(x:txs) ys@(y:tys)
  | x == y = x:union txs tys
  | x < y = x:union txs ys
  | x > y = y:union xs tys

fES :: Int -> Int
fES x = primes !! x where
  primes = 2:([3..] `minus` composites)
  composites = foldr unionP [] [multiples p | p <- primes]
  multiples n = map (n*) [n..]
  unionP (x:xs) ys = x:union xs ys

sMinus xs@(x:txs) ys@(y:tys)
  | x==y = sMinus txs tys
  | otherwise = x:sMinus txs ys

dUnion xs@(x:txs) ys@(y:tys)
  | x < y = x:dUnion txs ys
  | otherwise = y:dUnion xs tys
dUnion xs [] = xs

eSH :: Int -> Int
eSH x = primes !! x where
  composites (x:xs) = cmpsts where
    cmpsts = (x*x):map (x*) (dUnion xs cmpsts) `dUnion` (composites xs)
  primes = 2:([3..] `sMinus` composites primes)



nextWheel [] _ _ = [1]
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


eSW:: Int -> Int
eSW x = primes !! x where
  composites (p:ps) w =
    map (p*) (spin (circ w) p) `dUnionP` composites ps w' where
    w' = nextWheel1 w p
    dUnionP (x:xs) ys = x : dUnion xs ys
  primes = 2:([3..] `sMinus` (composites primes [1]))

eSI :: Int -> Int
eSI x = primes !! x where
  primes = 2:([3..] `sMinus` (composites primes [2..]))
  composites (p:ps) ss@(s:tss) = es `dUnionP` composites ps ss' where
    es = map (p*) ss
    ss' = tss `sMinus` es
    dUnionP (x:xs) ys = x : dUnion xs ys

eSPQ :: Int -> Int
eSPQ x = (sieve [2..]) !! x where
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


w4 = nextWheel1 [4,2,4,2,4,6,2,6] 7
s4 = spin (circ w4) 11

eSWPQ :: Int -> Int
eSWPQ x = primes !! x where
  sieve (c:cs) w = c:sieve' cs (nextWheel1 w c)
    (insert (c*c) (circ (map (c*) w)) empty) where 
      sieve' cs@(c:tcs) w tbl
        | c < n = c : sieve' tcs w' tbl'
        | otherwise = sieve' tcs w tbl'' where 
          (n, m:ms) = findMin tbl
          w' = nextWheel1 w c
          tbl' = insert (c*c) (circ (map (c*) w)) tbl
          tbl'' = insert (n+m) ms (deleteMin tbl)
  primes = 2:3:5:7:sieve s4 w4


tDat :: UnaryTestData Int
tDat  = 
  [ (100, return 100)
  , (300, return 300)
  , (600, return 600)
  , (900, return 900)
  , (1200, return 1200)
  , (1500, return 1500)
  , (1800, return 1800)
  , (2100, return 2100)
  , (2400, return 2400)
  , (2700, return 2700)
  , (3000, return 3000)
  , (3300, return 3300)
  , (3600, return 3600)
  , (3900, return 3900)
  , (4200, return 4200)
  , (4500, return 4500)
  , (4800, return 4800)
  , (5100, return 5100)
  , (5400, return 5400)
  , (5700, return 5700)
  ]

ts :: TestSuite 
ts  = def {
  _progs = ["uE", "eS", "fES", "eSH", "eSW", "eSI", "eSPQ", "eSWPQ"],
  _dataOpts = Manual "tDat"
}