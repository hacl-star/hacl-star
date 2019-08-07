{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

-- | Smth.

module Playground where

import Universum hiding (exp, last, (<*>))

import Data.List (delete, last, (!!))
import Data.Numbers.Primes (primeFactors, primes)
import System.Random (randomIO, randomRIO)

import Hacl
import Lib hiding (crt)


allEvenOrders :: Integer -> Bool
allEvenOrders n = all even $ mapMaybe (order n) [2..n-1]

units :: Integer -> [Integer]
units n = filter (\x -> gcd n x == 1) [1..n-1]

calcP :: Integer -> Int
calcP n = length $ filter (\x -> gcd n x == 1 && exp n x (n-1) == 1) [1..n-1]


isMthPrimRoot :: Integer -> Integer -> Integer -> Bool
isMthPrimRoot n m w = go w m
  where
    go acc pow = if pow == 1 then acc == 1 else acc /= 1 && go ((acc * w) `mod` n) (pow-1)

findMthPrimRoot :: Integer -> Integer -> Maybe Integer
findMthPrimRoot n m = find (isMthPrimRoot n m) [0..n-1]

testFindPrimRoot :: IO ()
testFindPrimRoot = do
    let s = 128
    let genPrimes i = do
            p <- genPrime 20
            q <- genPrime 20
            let lam = lcm (p-1) (q-1)
            if lam `mod` s == 0
               -- && isPrime (lam `div` s)
                then pure (p,q,i) else genPrimes (i+1)
    (p,q,i) <- genPrimes 0
    putTextLn $ "Iteration: " <> show i
    let n = p * q
    let lam = lcm (p-1) (q-1)
    let lamFactors = ordNub $ 1024 : primeFactors (lam `div` 1024)

    let isGen g =
            gcd g n == 1 &&
            all (\factor -> exp n g factor /= 1) lamFactors &&
            exp n g lam == 1

    let tryGen j = if i == 0 then pure Nothing else do
            let lroot :: Integer = fromMaybe (error "should work") $ find isGen [1..]
            let mroot = exp n lroot (lam `div` s)
            if isMthPrimRoot n 4 mroot then pure (Just mroot) else tryGen (j-1)

    tryGen 10 >>= \case
        Nothing -> testFindPrimRoot
        Just mroot -> putTextLn $ show mroot

carm :: Integer -> Integer
carm x =
    let fs = primeFactors x in
    let fsn = ordNub fs in
    case fsn of
      [_] -> fromIntegral $
          if (length fs > 2) then eulerPhiFast x `div` 2 else eulerPhiFast x
      xs  -> foldr1 lcm $ map carm xs

type Nt = Z 323 -- 19 * 17
type Nst = Z 3515706497843 -- n ^ 5




-- (uvr_p + 1)(uvr_q + 1)
-- + find g / h

----------------------------------------------------------------------------
-- Inspecting FFT domain automorhisms
----------------------------------------------------------------------------

-- List of powers of w_n
type El n = [Z n]

type Pack n = [El n]

rotateRight :: [a] -> [a]
rotateRight xs = last xs : take (length xs - 1) xs

rotateRightTimes :: Int -> [a] -> [a]
rotateRightTimes 0 x = x
rotateRightTimes j x = rotateRightTimes (j-1) (rotateRight x)

opRotate :: Pack n -> Pack n
opRotate = rotateRight

opMulWj :: KnownNat n => Z n -> Pack n -> Pack n
opMulWj wj = map (map (<+> wj))

fftGen :: forall n. KnownNat n => Pack n
fftGen =
    let n' = natValI @n in
    map (\i -> map (\j -> Z i <*> Z j) [0..n'-1]) [0..n'-1]

allGroupComb :: forall n. KnownNat n => [Pack n -> Pack n]
allGroupComb =
    let n' = fromIntegral $ natValI @n in
    (rotateRightTimes <$> [0..n'-1]) ++
    (opMulWj <$> map (toZ . fromIntegral) [0..n'-1])

discoverAllElems :: forall n. KnownNat n => IO ()
discoverAllElems = do
    let n' = fromIntegral $ natValI @n
    let orig = fftGen @n
    let addMore (packs :: [Pack n]) depth =
          if depth > 10 then packs else
          let packs' = ordNub (packs ++ concatMap (\pack -> map (\a -> a pack) allGroupComb) packs) in
          if length packs' == length packs then packs else addMore packs' (depth+1)
    let saturated = addMore [orig] 0

    let origShifts = concatMap (\el -> map (\sh -> sh el) (rotateRightTimes <$> [0..n'-1])) orig
    let ofShifts (x::Pack n) = all (`elem` origShifts) x

    print (length saturated)
    forM_ saturated print
    putTextLn "\nFiltered:"
    let filtered = filter ofShifts saturated
    print (length filtered)
    forM_ filtered print

----------------------------------------------------------------------------
-- DJ FFT packing prototype
----------------------------------------------------------------------------

data DJParams =
    DJParams
        {
          djm    :: Integer
        , djN    :: Integer
        , djw    :: Integer
        , djwInv :: Integer -- modulo N
        , djn    :: Integer
        , djnInv :: Integer -- modulo N
        , djU    :: Integer
        , dju    :: Integer -- slot size, such that U = u ^ n -1
        } deriving (Show)

-- finds prime k * n + 1 that it's more than m
genFFTModulus :: Integer -> Integer -> (Integer,Integer)
genFFTModulus n m = go (m `div` n + 1)
  where
    go k = if isPrimeMR 40 (k*n + 1) then (k, k*n+1) else go (k + 1)

-- Finds generator of multiplicative group of Z_n
findGen :: Integer -> Integer
findGen n =
    fromMaybe (error $ "findGenerator: didn't manage to, the group is not cyclic") $
    find (\g -> order n g == Just (n-1)) [1..n-1]

findFFTRoot :: Integer -> Integer -> Integer
findFFTRoot k djN = exp djN (findGen djN) k

genDJParams :: Integer -> Integer -> Integer -> DJParams
genDJParams djn djm slotBits =
    let (k, djN) = genFFTModulus djn djm in
    let djw = findFFTRoot k djN in
    let djwInv = inverse djw djN in
    let djnInv = inverse djn djN in
    let dju = djN * (2 ^ slotBits) in -- N + extra bits required
    let djU = dju ^ djn - 1 in
    DJParams {..}

simdadd :: Num a => [a] -> [a] -> [a]
simdadd x y = map (uncurry (+)) (zip x y)

simdmul :: Num a => [a] -> [a] -> [a]
simdmul x y = map (uncurry (*)) (zip x y)

dotprod :: [Integer] -> [Integer] -> Integer
dotprod x y = sum $ simdmul x y

fftRaw :: Integer -> Integer -> Integer -> [Integer] -> [Integer]
fftRaw djN n w ax = map (\j -> dotprod (row j) ax) [0..n-1]
  where
    row1 = map (\i -> exp djN w i) [0..n-1]
    row :: Integer -> [Integer]
    row i = map (\wi -> exp djN wi i) row1

fft :: DJParams -> [Integer] -> [Integer]
fft DJParams{..} = fftRaw djN djn djw

fftinv :: DJParams -> [Integer] -> [Integer]
fftinv DJParams {..} =
    map (\x -> (djnInv * x) `mod` djN) .
    fftRaw djN djn djwInv

-- standard poly conv
conv :: [Integer] -> [Integer] -> [Integer]
conv a b = if length a /= length b then error "mda" else
    map ck [0..2*n-2]
  where
    n = length a
    l = [0..n-1]
    inRange x = x >= 0 && x < n
    ck k =
        foldr1 (+) $
        map (\(i,j) -> (a !! i) * (b !! j))
            [(i,j) | i <- l, j <- l, inRange i, inRange j, i + j == k]

convRound :: [Integer] -> [Integer] -> [Integer]
convRound a b = if length a /= length b then error "mda" else
    map ck [0..n-1]
  where
    n = length a
    l = [0..n-1]
    inRange x = x >= 0 && x < n
    ck k =
        foldr1 (+) $
        map (\(i,j) -> (a !! i) * (b !! j))
            [(i,j) | i <- l, j <- l, inRange i, inRange j, (i + j) `mod` n == k]

evalCircularShift :: IO ()
evalCircularShift = do
    let n = 4
    let params@DJParams{..} = genDJParams n 1024 20
    let a = fft params [5,6,7,8]
    let shft1 (x:xs) = xs ++ [x]
    let shft n l = if n == 0 then l else shft (n-1) (shft1 l)

    print $ fftinv params a
    print $ fftinv params $ shft 1 a
    print $ fftinv params $ shft 2 a
    print $ fftinv params $ shft 3 a
    print $ fftinv params $ shft 4 a


    print $ fftinv params $ foldr1 simdadd [a, shft 1 a, shft 2 a, shft 3 a]

fftTest1 :: IO ()
fftTest1 = do
    let n = 4
    let n2 = 2 * n
    let params@DJParams{..} = genDJParams n2 1024 20
    let a = [3..(n+2)]
    let b = [2..(n+1)]
    let red = map (`mod` djN)
    let a' = red $ fft params a
    let b' = red $ fft params b
    let c' = red $ simdmul a' b'
    let d = fftinv params c'
    print d
    print $ conv a b

fftTest2 :: IO ()
fftTest2 = do
    let n = 16
    let m = 1024
    let params@DJParams{..} = genDJParams n m 100
    print djN
    let a = replicate (fromIntegral n) 2
    let b = replicate (fromIntegral n) 100
    let a' = fft params a
    let b' = fft params b

    -- Without psi
    print (simdmul a b)
    print (convRound a' b')
    let c' = map (* inverse n djN) $ map (`mod` djN) $ convRound a' b'
    let c = fftinv params c'
    print (c == simdmul a b)

    -- With psi
    let d' = (psi dju a' * psi dju b') `mod` djU
    print (d' == psi dju (convRound a' b'))
    let d = fftinv params $ psiinv dju $ d' * inverse n djN
    print $ d == simdmul a b

-- modular
fftTest3 :: IO ()
fftTest3 = do
    let n = 16
    let m = 1024
    let params@DJParams{..} = genDJParams n m 100
    print djN
    let a = replicate (fromIntegral n) 1023
    let b = replicate (fromIntegral n) 1023
    let a' = fft params a
    let b' = fft params b

    -- Without psi
    let c' = map (* inverse n djN) $ map (`mod` djN) $ convRound a' b'
    let c = fftinv params c'
    print (c == (map (`mod` djN) $ simdmul a b))

    -- With psi
    let d' = (psi dju a' * psi dju b') `mod` djU
    print (d' == psi dju (convRound a' b'))
    let d = fftinv params $ psiinv dju $ d' * inverse n djN
    print $ d == map (`mod` djN) (simdmul a b)

fftTest4 :: IO ()
fftTest4 = do
    let n = 8
    let m = 1024
    let params@DJParams{..} = genDJParams n m 100
    print djN
    let a = [5,6,0,0,0,0,0,0]
    let a' = fft params a

    -- With psi
    let d' = (psi dju a' + dju * 2) `mod` djU
    let d = fftinv params $ psiinv dju $ d' * inverse n djN
    print d

psi :: Integer -> [Integer] -> Integer
psi m ax = dotprod (map (m ^) [0..(length ax - 1)]) ax

psiinv :: Integer -> Integer -> [Integer]
psiinv m ax = if ax < m then [ax] else ax `mod` m : psiinv m (ax `div` m)

testpsi :: IO ()
testpsi = do
    let m = 1024
    let n = 4
    let a = [1..n]
    let b = [5..n+4]
--    let b = [1023-2*n..1023-n-1]
    let a' = psi m a
    let b' = psi m b
    print (psiinv m a' == a)
    print (psiinv m b' == b)
    print (psiinv m (a' + b') == simdadd a b)
    print (psiinv m ((a' * m) `mod` (m^n-1)) == rotateRight a)
    print (psiinv m ((a' * b') `mod` (m^n-1)) == convRound a b)

suitablePrm :: Int -> Integer -> Bool
suitablePrm 0 p = isPrimeMR 40 p
suitablePrm i p =
    let base = [2..50] in
    case find (\x -> p `mod` x == 0) base of
        Just y  -> suitablePrm (i-1) (p `div` y)
        Nothing -> isPrimeMR 40 p

isBSmooth:: Integer -> Integer -> Bool
isBSmooth _ 0 = True
isBSmooth bound p =
    case find (\x -> p `mod` x == 0) [2..bound] of
      Just y  -> isBSmooth bound (p `div` y)
      Nothing -> False

findU :: Integer -> Integer -> Integer -> IO Integer
findU att u0 s = do
    let p = u0 ^ s - 1
    putStr ("." ::Text)
--    print p
--    print (length (primeFactors p))
--    if length (primeFactors p) < 10
--    if isPrimeMR 20 p
--    if suitablePrm 10 p
    if isBSmooth 100 p
        then pure p else findU (att+1) (u0-1) s

-- Unencrypted integer, wrapper made for functionality testing
-- purpuses only
data DJMsg = DJMsg { unDJMsg :: Integer } deriving Show

djHomAdd :: DJParams -> DJMsg -> DJMsg -> DJMsg
djHomAdd DJParams{djU} (DJMsg a) (DJMsg b) = DJMsg ((a+b) `mod` djU)

djHomMulScal :: DJParams -> DJMsg -> Integer -> DJMsg
djHomMulScal DJParams{djU} (DJMsg a) k = DJMsg ((a*k) `mod` djU)

djHomSIMDProd :: DJParams -> DJMsg -> [Integer] -> DJMsg
djHomSIMDProd params@DJParams{..} m vec =
    let (DJMsg m') = djHomMulScal params m (psi dju $ fft params vec) in
    DJMsg (m' * djnInv)


djFFT params@DJParams{..} w msg =
    -- mul by fft matrix
--    traceShow msg $
    let m1 = map (\i -> djHomSIMDProd params msg (wrow i)) [0..djn-1] in
--    traceShow (map (\(DJMsg x) -> x `mod` djN) m1) $
--    traceShow (map (\(DJMsg x) -> x) m1) $
    -- sum them all completing fft
    let m2 = foldr1 (djHomAdd params) m1 in
    m2
  where
    wrow i = map (\wi -> exp djN wi i) (map (\j -> exp djN w j) [0..djn-1])
--    wrow i = map (^ i) (map (w ^) [0..djn-1])


djRotate :: DJParams -> DJMsg -> Integer -> DJMsg
djRotate params@DJParams{..} m s = do
    let m1 = djFFT params djw m

--    let m2 = djHomSIMDProd params m1 (wrow djw s)

    let m3 = djHomMulScal params (djFFT params djwInv m1) djnInv

    m3

testSIMDAddMul :: IO ()
testSIMDAddMul = do
    let n = 4
    let params@DJParams{..} = genDJParams n 1024 100
    let m1 = [5,6,7,8]
    let m2 = [2,3,4,5]

    let msg1 = DJMsg (psi dju m1)
    let msg2 = DJMsg (psi dju m2)
    let msg3 = psiinv dju $ unDJMsg $ djHomAdd params msg1 msg2
    print (msg3 == simdadd m1 m2)


    let dec = fftinv params . psiinv dju . unDJMsg

    let msg4 = DJMsg (psi dju $ fft params m1)
    let msg5 = DJMsg (psi dju $ fft params m2)
    let msg6 = djHomAdd params msg4 msg5
    print (dec msg6 == simdadd m1 m2)
    let msg7 = djHomSIMDProd params msg4 m2
    print (dec msg7 == simdmul m1 m2)


testRotate :: IO ()
testRotate = do
    let n = 4
    let params@DJParams{..} = genDJParams n 1024 1000
    print djN
    let m = [3,6,4,9]
--    let msg = DJMsg (psi dju (fft params m))
--    let msg2 = fftinv params $ psiinv dju $ unDJMsg $ djFFT params djw msg
--    --let msg2 = fftinv params $ psiinv dju $ unDJMsg $ djRotate params msg 1
--    print (map (`mod` djN) msg2 == map (`mod` djN) (fft params m))
--    print msg2
--    print $ fft params m

    let msg = fft params m
    let dec = fftinv params

    let djHomSIMDProd' :: [Integer] -> [Integer] -> [Integer]
        djHomSIMDProd' m0 vec =
          let m' = convRound m0 (fft params vec) in
          map (* djnInv) m'


    let wrow w i = map (\wi -> exp djN wi i) (map (\j -> exp djN w j) [0..djn-1])

    let testMul vec = do
            let m' = djHomSIMDProd' msg vec
            print vec
            print $ fft params vec
            print (dec m' == (map (`mod` djN) $ simdmul m vec))

    testMul (wrow djw 0)
    testMul $ replicate 4 258
    testMul $ replicate 4 259
    testMul (wrow djw 1)


    let m1 = map (\i -> djHomSIMDProd' msg (wrow djw i)) [0..djn-1]

    print (map dec m1 == map (\i -> map (`mod` djN) $ simdmul m (wrow djw i)) [0..djn-1])

    print $ map (map (`mod` djN) . dec) m1

    let m2 = foldr1 simdadd m1
    print $ dec m2

----------------------------------------------------------------------------
-- CRT embedding
----------------------------------------------------------------------------

crt' :: [(Integer,Integer)] -> Integer
crt' [] = error "chinese called with empty list"
crt' xs | not (coprimes $ map snd xs) =
             error $ "not relative primes: " <> show (map snd xs)
crt' ((a1,m1):xs0) = chineseGo xs0 a1 m1
  where
    chineseGo [] c _              = c
    chineseGo ((a, m):xs) c mprod =
        chineseGo xs c' (mprod * m)
        where
          m' = inverse mprod m
          --y = (m' * ((a - c) `mod` m)) `mod` m
          y = (m' * ((a - c) `mod` m)) `mod` (m*m)
          c' = c + mprod * y

crt :: [Integer] -> [Integer] -> Integer
crt base vals = crt' $ vals `zip` base

crtInv :: [Integer] -> Integer -> [Integer]
crtInv base v = map (v `mod`) base

crtBound :: IO ()
crtBound = do
    let n = 3
    let m = 31
    let base = take n $ filter (> m) primes
    print $ product base
    print $ maximum $ map (crt base) $ replicateM n [0..m]


crtSame :: IO ()
crtSame = do
    let n = 3
    let m = 1024
    let base = take n $ filter (> m) primes
    let base' = take (n-2) base ++ [base !! (n-1)] ++ [base !! (n-2)]

    print $ crt base [0,3,4]
    print $ crt base' [0,4,3]
    print $ crtInv base $ crt base [0,3,4]
    print $ crtInv base' $ crt base' [0,4,3]


testCrt :: IO ()
testCrt = do
    let n = 4
    let m = 1024
    let allPrimes = take (n+1) $ filter (> m) primes
    let base = take n allPrimes
    let baseprod = product base
--    let findq x = if isPrimeMR 40 x then pure x else findq (x+1)
--    q <- findq (product base + 1)
    let q = allPrimes !! n
    let u = q ^ n
    let m0 = [1021,1021,1021,1021]
    let m1 = [2,2,2,2]
    let m2 = [511,511,511,511]

    let bi i = product (delete (base !! i) base)
    let biinv j = inverse (bi j) (base !! j)

    print base
    print baseprod
    print $ crt base [2,3,4,5] * crt base [195,196,197,198]
    print $ crtInv base $ crt base [2,3,4,5] * crt base [195,196,197,198]
    print $ crtInv base $ (crt base [2,3,4,5] * crt base [195,196,197,198]) `mod` baseprod
    print $ crtInv base $ (crt base [2,3,4,5] * crt base [195,196,197,198]) `mod` (2 * baseprod)
    print $ crtInv base $ (crt base [2,3,4,5] * crt base [195,196,197,198]) `mod` u
    print $ crt base m1
    print $ crtInv base $ crt base m1
    print $ crtInv base $ crt base m0 + crt base m1
    print $ crtInv base $ crt base m1 * crt base m2
    print $ crtInv base $ (crt base m1 * crt base m2) `mod` baseprod
    print $ crtInv base $ crt base m2 * crt base [0,0,1,1]


    let p1 j = bi j * ((1 - bi j * biinv j) `mod` (base !! j))
    let d j = (p1 j + bi j * 5 * biinv j)
    let d' j = bi j * ((5 * biinv j) `mod` (base !! j))
    let d'' j = bi j * (5 * biinv j)

    print "--"
    print $ crt base [0,0,5,0]
    print $ d 2
    print $ d' 2
    print $ d'' 2 -- same as d 2

    print "--"
    print $ crt base [0,0,0,5]
    print $ d 3
    print $ d' 3
    print $ d'' 3 -- same as d 2 and crt


    let switch i j x =
            let pre = ((x + (u-p1 i)) * (inverse (bi i * biinv i) u)) `mod` u in
            pre * bi j * biinv j + p1 j

    let switch' i j x =
            let pre = (x * (inverse (bi i * biinv i) u)) `mod` u in
            pre * bi j * biinv j

    print "--"
    print $ crtInv base $ switch' 3 2 $ crt base [0,0,0,5]
    print $ crtInv base $ switch' 2 3 $ crt base [0,0,5,0]
    print $ crtInv base $ switch' 2 1 $ d'' 2

    print "--"
    print $ crtInv base (d' 2)
    print $ crtInv base (d 2)
    print $ crtInv base (d 2 `mod` baseprod)
    print $ crtInv base $ switch 2 3 (d 2)
    print $ crtInv base $ switch 2 3 (crt base [0,0,5,0])

    -- REALS

--    print $ crtInv base $ (crt base [5,25,101,25000] * crt base (map (inverse 5) base)) `mod` u

--    let encReal x = round $ x * 100
--    let l1 = [5.21, 7.92, 14.6, 2.24]
--    let l2 = [2.36, 5.51, 4.97, 1.90]
--    let r1 = crt base $ map encReal l1
--    let r2 = crt base $ map encReal l2
--    print $ simdmul l1 l2
--    print $ crtInv base $ r1 * r2
--    print $ crtInv base $ r1 * r2 * crt base (map (inverse 100) base)

-- | Inverse for non-primes
inverse' :: (Integral n, Show n) => n -> n -> n
inverse' a n =
    if gcd' /= 1 then error  $ "inverse: gcd is not 1: " <> show (a,n,gcd')
                 else u `mod` n
  where
    (gcd',u,_) = exEucl a n


crt'' :: [(Integer,Integer)] -> Integer
crt'' [] = error "chinese called with empty list"
crt'' xs | not (coprimes $ map snd xs) =
             error $ "not relative primes: " <> show (map snd xs)
crt'' l = chineseGo l [] 1
  where
    chineseGo [] _ c          = c
    chineseGo ((a, m):xs) ms c =
        traceShow (g',c') $
        chineseGo xs (m:ms) c'
      where
        g' = crt (m:ms) (inverse' c m : map (\mi -> inverse' a mi) ms)
        c' = if a == 0
             then c * m * crt ms (map (\mi -> inverse' m mi) ms)
             else c * a * g'

crtWeird :: [Integer] -> [Integer] -> Integer
crtWeird base vals = crt'' $ vals `zip` base

testCrtWeird :: IO ()
testCrtWeird = do
    let m = 15
    let n = 4
    let base = take n $ filter (> m) primes
    print base
    print $ crtWeird base [1,2,4,5]
    print $ crtInv base $ crtWeird base [1,2,4,5]

testEqSolve :: IO ()
testEqSolve = do

    let a = 8
    let c = 531511512
    let solve y = let z = crt [17, 19, 23] $ map (inverse y) [17, 19, 23] in
                  let y' = a * (inverse (c * z) 29) in
                  if y == y' then y else solve y'

    print $ solve 1
    putTextLn "mda"


crt3 :: [Integer] -> [Integer] -> Integer
crt3 base vals = sum $ map (\(p,a) -> a * b p * inverse (b p) p) $ zip base vals
  where
    b p = product base `div` p
    --b p = (product base * product base) `div` (p*p)

testCrt3 :: IO ()
testCrt3 = do
    let m = 15
    let n = 4
    q <- genPrime 80
    let base = take n $ filter (> m) primes
    print base
    let m1 = [1,5,9,4]
    print $ crt3 base m1
    print $ crtInv base $ crt3 base m1
    print $ crtInv base $ crt3 base m1 + crt3 base [5,5,5,5]
    print $ crtInv base $ crt3 base m1 * crt3 base [5,5,5,5]
    print $ crtInv base $ crt3 base m1 * crt3 base [0,0,1,0]

    putTextLn "-----"

    let p i = base !! i
    let b i = product base `div` p i
    let binv i = inverse (b i) (p i)


    let switch i j x = (x * inverse (b i * binv i) q * b j * binv j) `mod` q
    let switch2 i j x = (x * inverse (p j * binv i) q * p i * binv j) `mod` q
    let switch3 i j k x = (x * inverse ((b i * binv i) ^ k) q * b j * binv j) `mod` q
    let cancel4 i k x = (x * inverse ((b i * binv i) ^ k) q) `mod` q

    print $ crtInv base $ switch 2 1 $ crt3 base [0,0,1,0]
    print $ crtInv base $ switch 2 1 $ crt3 base [0,0,1,0] + crt3 base [0,0,5,0]

    print $ crtInv base $ switch 2 1 $ crt3 base [0,0,1,0] * crt3 base [0,0,1,0]
    print $ crtInv base $ switch 2 1 $ crt3 base m1 * crt3 base [0,0,1,0]
    print $ crtInv base $
        switch2 2 1 $
        cancel4 2 1 $
        crt3 base m1 * (crt3 base [0,0,1,0] + product base * product base)
    print $ crtInv base $ switch2 2 1 $
        crt3 base m1 * (crt3 base [0,0,1,0] + product base * product base)

    putTextLn "*****"

    print $ crtInv base $ switch2 2 1 $ crt3 base [0,0,1,0]
    print $ crtInv base $ switch2 2 1 $ crt3 base [0,0,1,0] + crt3 base [0,0,5,0]

    print $ crtInv base $ switch2 2 1 $ crt3 base m1 * crt3 base [0,0,1,0]
    print $ crtInv base $ switch2 2 2 $ crt3 base m1 * crt3 base [0,0,1,0]
    print $ crtInv base $ switch2 2 3 $ crt3 base m1 * crt3 base [0,0,1,0]

    putTextLn "*****"

    print $ crtInv base $ switch3 2 1 1 $ crt3 base [0,0,1,0]
    print $ crtInv base $ switch3 2 1 1 $ crt3 base [0,0,1,0] + crt3 base [0,0,5,0]

    print $ crtInv base $ switch3 2 1 2 $ crt3 base [0,0,1,0] * crt3 base [0,0,1,0]
    print $ crtInv base $ switch3 2 1 2 $ crt3 base m1 * crt3 base [0,0,1,0]
    print $ crtInv base $ switch3 2 2 2 $ crt3 base m1 * crt3 base [0,0,1,0]
    print $ crtInv base $ switch3 2 3 2 $ crt3 base m1 * crt3 base [0,0,1,0]

foo :: Double -> Double
foo n = (2 * n - 2 + sqrt ((2 - 2 * n) ^ 2 - 4 * (n-2)* (n-1) )) / (2 * (n-2))

----------------------------------------------------------------------------
-- WOW
----------------------------------------------------------------------------
