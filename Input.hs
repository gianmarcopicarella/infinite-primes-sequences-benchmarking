module Input where 

import Data.PQueue.Prio.Min (empty, insert, findMin, deleteMin)
import Data.Default (def)
import AutoBench.QuickCheck
import AutoBench.Types

import Test.QuickCheck (Arbitrary(..), sized)
import Control.DeepSeq (NFData(..))


uE :: PositiveInt -> Int
uE (PositiveInt x) = (filterPrime [2..]) !! x where
  filterPrime (p:xs) =
    p : filterPrime [x | x <- xs, (mod x p) /= 0]

minus xs@(x:txs) ys@(y:tys)
  | x < y = x : minus txs ys
  | x > y = minus xs txs
  | otherwise = minus txs tys

eS :: PositiveInt -> Int
eS (PositiveInt x) = (eulerSieve [2..]) !! x where
  eulerSieve cs@(p:tcs) = p:eulerSieve (minus tcs (map (p*) cs))


union xs@(x:txs) ys@(y:tys)
  | x == y = x:union txs tys
  | x < y = x:union txs ys
  | x > y = y:union xs tys

fES :: PositiveInt -> Int
fES (PositiveInt x) = primes !! x where
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

eSH :: PositiveInt -> Int
eSH (PositiveInt x) = primes !! x where
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


eSW:: PositiveInt -> Int
eSW (PositiveInt x) = primes !! x where
  composites (p:ps) w =
    map (p*) (spin (circ w) p) `dUnionP` composites ps w' where
    w' = nextWheel1 w p
    dUnionP (x:xs) ys = x : dUnion xs ys
  primes = 2:([3..] `sMinus` (composites primes [1]))

eSI :: PositiveInt -> Int
eSI (PositiveInt x) = primes !! x where
  primes = 2:([3..] `sMinus` (composites primes [2..]))
  composites (p:ps) ss@(s:tss) = es `dUnionP` composites ps ss' where
    es = map (p*) ss
    ss' = tss `sMinus` es
    dUnionP (x:xs) ys = x : dUnion xs ys

eSPQ :: PositiveInt -> Int
eSPQ (PositiveInt x) = (sieve [2..]) !! x where
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

eSWPQ :: PositiveInt -> Int
eSWPQ (PositiveInt x) = primes !! x where
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


newtype PositiveInt = PositiveInt Int deriving Show

instance Arbitrary PositiveInt where
  arbitrary = sized(\n -> 
    if n < 0 
    then error $ "valore negativo" ++ show n
    else return $ PositiveInt n)

instance NFData PositiveInt where 
  rnf (PositiveInt n) = rnf n

ts  = def {
  _progs = ["uE", "eS", "fES", "eSH", "eSW", "eSI", "eSPQ", "eSWPQ"],
  _dataOpts = Gen 0 500 10000
}
