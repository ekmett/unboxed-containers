import System.Random
import System.TimeIt
import Control.Exception (evaluate)
import Control.Parallel.Strategies

import qualified Data.Set as S
import qualified Data.IntSet as I
import qualified Data.Set.Unboxed as U

eval m x = putStr (m ++ " ") >> timeIt (evaluate x)
forceList m l = eval m (l `using` parList rnf)

n = 2^18

instance (Random x, Random y) => Random (x,y) where
    random g = ((a,b),g'') where
        (a,g') = random g
        (b,g'') = random g'
    randomR ((la,lb),(ha,hb)) g = ((a,b),g'') where
        (a,g') = randomR (la,ha) g
        (b,g'') = randomR (lb,hb) g'

instance (Random x, Random y,Random z) => Random (x,y,z) where
    random g = ((a,b,c),g''') where
        (a,g') = random g
        (b,g'') = random g'
        (c,g''') = random g''
    randomR ((la,lb,lc),(ha,hb,hc)) g = ((a,b,c),g''') where
        (a,g') = randomR (la,ha) g
        (b,g'') = randomR (lb,hb) g'
        (c,g''') = randomR (lc,hc) g''

instance (Random w, Random x, Random y,Random z) => Random (w,x,y,z) where
    random g = ((a,b,c,d),g'''') where
        (a,g') = random g
        (b,g'') = random g'
        (c,g''') = random g''
        (d,g'''') = random g'''
    randomR ((la,lb,lc,ld),(ha,hb,hc,hd)) g = ((a,b,c,d),g'''') where
        (a,g') = randomR (la,ha) g
        (b,g'') = randomR (lb,hb) g'
        (c,g''') = randomR (lc,hc) g''
        (d,g'''') = randomR (ld,hd) g'''

main = do
    let g  = mkStdGen 42
        rs :: [Int]
        rs = take n (randoms g)
    forceList "Generating random numbers" rs
    testB rs
    testU rs
    test rs
    -- testI rs

test rs = do
    s <- eval "constructing Set         " $ S.fromList rs
    forceList "Set.member               " $ map (flip S.member s) rs

testB rs = do
    s <- eval "constructing BoxedSet    " $ U.fromList (map U.Boxed rs)
    forceList "BoxedSet.member          " $ map (flip (U.member . U.Boxed) s) rs

testU rs = do
    s <- eval "constructing USet        " $ U.fromList rs
    forceList "USet.member              " $ map (flip U.member s) rs

{-
testI rs = do
    s <- eval "constructing IntSet      " $ I.fromList rs
    forceList "IntSet.member            " $ map (flip I.member s) rs
-}
