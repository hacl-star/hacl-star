{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DefaultSignatures   #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeInType          #-}

-- | Finite fields and stuff. TODO rename/decouple it.

module Lib.Field
    ( AGroup (..)
    , fabs
    , linearTimes
    , fastTimes
    , Ring(..)
    , (<->)
    , linearExp
    , fastExp
    , Field(..)
    , Finite(..)
    , fermatInverse
    , FField(..)
    , Euclidian(..)
    , eDiv
    , eMod

    , findGenerator
    , gcdEucl
    , extendedEucl
    , findRoots

    , natValI
    , Z (..)
    , toZ
    , PrimeNat
    , Poly(..)
    , stripZ
    , prettyPoly
    , deg
    , applyPoly
    , euclPoly


    , represent
    , representBack
    , getCoeffPoly

    , PolyDivisor (..)
    , representConv
    , representBackConv

    , FinPoly (..)
    , FinPolyZ
    , mkFinPoly
    , isPrimePoly
    , FinPolyNats
    , PrimePoly
    , irreducablePoly
    , invPolyEuclidian

    ) where

import qualified Prelude
import Universum hiding (head, (<*>))

import Control.Lens (ix, makeWrapped)
import Data.List ((!!))
import qualified Data.List as L

----------------------------------------------------------------------------
-- Typeclasses and misc
----------------------------------------------------------------------------

-- Disclaimer: this hierarchy is not optimal. For instance,
-- multiplicative groups can't be exressed at all :shrug:.

-- Addition group.
class Eq a => AGroup a where
    f0 :: a

    infixl 5 <+>
    (<+>) :: a -> a -> a

    fneg :: a -> a

    -- In case it can be implemented more efficiently.
    infixl 6 `times`
    times :: Integer -> a -> a
    default times :: Integer -> a -> a
    times = fastTimes f0 fneg (<+>)

infixl 5 <->
(<->) :: AGroup a => a -> a -> a
(<->) a b = a <+> (fneg b)

-- | Absolute value.
fabs :: (AGroup a, Ord a) => a -> a
fabs x = if x > f0 then x else fneg x

-- These functions are implemented w/o typeclass for flexibility --
-- there are also other parts of lib (like, vectors) that don't use
-- AGroup, but would like to have 'times'.
-- | Slow linear "times" implementation.
linearTimes :: forall x. x -> (x -> x) -> (x -> x -> x) -> Integer -> x -> x
linearTimes z neg add n0 a0 = go n
  where
    (n,a) = if n0 < 0 then (negate n0, neg a0) else (n0,a0)
    -- because folds imply construction of a (potentially long) list
    go m = if m == 0 then z else add a (go (m-1))

-- | Double-and-add.
fastTimes :: a -> (a -> a) -> (a -> a -> a) -> Integer -> a -> a
fastTimes z neg add n0 a0 = tms n
  where
    (n,a) = if n0 < 0 then (negate n0, neg a0) else (n0,a0)
    tms 0 = z
    tms 1 = a
    tms m = do
        let (mdiv,mmod) = m `divMod` 2
        let mnext = tms mdiv
        if | mmod == 0 -> mnext `add` mnext
           | otherwise -> mnext `add` mnext `add` a

class (Eq a, AGroup a) => Ring a where
    f1 :: a

    infixl 6 <*>
    (<*>) :: a -> a -> a

    infixl 7 <^>
    (<^>) :: a -> Integer -> a
    default (<^>) :: a -> Integer -> a
    (<^>) = fastExp

-- | Linear exponentiation by multiplication.
linearExp :: Ring a => a -> Integer -> a
linearExp a n = foldl' (<*>) f1 $ replicate (fromIntegral n) a

-- | Fast powering algorithm for calculating a^p (mod p).
fastExp :: forall a n . (Ring a, Integral n) => a -> n -> a
fastExp g n = power g n
  where
    power :: a -> n -> a
    power _ 0 = f1
    power a 1 = a
    power a b = do
        let (bdiv,bmod) = b `divMod` 2
        let bnext = a `power` bdiv
        if | bmod == 0 -> bnext <*> bnext
           | otherwise -> bnext <*> bnext <*> a

-- | Searchs for the generator given op and list of elements to
-- produce (also to choose from). For multiplicative group it should
-- be used with (<*>) and (allElems \\ f0), since 0 is not produced.
findGenerator :: forall a. (Eq a) => (a -> a -> a) -> [a] -> a
findGenerator op els =
    fromMaybe (error $ "findGenerator: didn't manage to") $
    find (\g -> let s = genOrderSet [] g g in length s == n) els
  where
    n = length els
    genOrderSet acc g0 g | g `elem` acc = acc
                         | otherwise = genOrderSet (g:acc) g0 (g `op` g0)

-- Field.
class Ring a => Field a where
    finv :: a -> a
    -- ^ Multiplicative inverse.

class Eq a => Finite a where
    allElems :: [a]
    -- ^ List all elements.
    getOrder :: Integer
    -- ^ Return number of elements

    default allElems :: FField a => [a]
    allElems =
        let (g :: a) = getGen
            genPowers = iterate (g <*>) g
        -- f0 + powers
        in f0:(dropWhile (/= f1) genPowers)

    default getOrder :: Integer
    getOrder = fromIntegral $ length (allElems @a)

-- Finite field.
class (Finite a, Field a) => FField a where
    getGen :: a
    -- ^ Generator.

    default getGen :: a
    getGen = findGenerator (<*>) (L.delete f0 allElems)

-- | Compute inverse using fermat's algorithm. It doesn't work in all
-- cases, but only for rings where fermat's theorem holds.
fermatInverse :: forall f. (Finite f, Ring f) => f -> f
fermatInverse x =
    let phi = fromInteger $ getOrder @f - 1
        res = x <^> (phi - 1)
    in if res <*> x /= f1 then error "fermatInverse failed" else res

----------------------------------------------------------------------------
-- Integer
----------------------------------------------------------------------------

instance AGroup Integer where
    f0 = 0
    (<+>) = (+)
    fneg = negate

instance Ring Integer where
    f1 = 1
    (<*>) = (*)

----------------------------------------------------------------------------
-- Double/rational
----------------------------------------------------------------------------

instance AGroup Double where
    f0 = 0
    (<+>) = (+)
    fneg = negate

instance Ring Double where
    f1 = 1
    (<*>) = (*)

instance Field Double where
    finv x = 1/x


instance AGroup Rational where
    f0 = 0
    (<+>) = (+)
    fneg = negate

instance Ring Rational where
    f1 = 1
    (<*>) = (*)

instance Field Rational where
    finv x = 1/x

----------------------------------------------------------------------------
-- Prime nats
----------------------------------------------------------------------------

class KnownNat n => PrimeNat (n :: Nat)

-- Sadly, I do not know a better way to solve this problem. It'd be
-- nice if GHC ran primality test every time he was checking the
-- instance. I think I could at least use TH to pre-generate first k
-- primes. Also if this is tedious to use, one can just define
-- "instance KnownNat n => PrimeNat n" and forget about this check.
#define DefPrime(N) instance PrimeNat N;\

DefPrime(2)
DefPrime(3)
DefPrime(5)
DefPrime(7)
DefPrime(9)
DefPrime(11)
DefPrime(13)
DefPrime(17)
DefPrime(19)
DefPrime(23)
DefPrime(29)
DefPrime(41)
DefPrime(47)
DefPrime(53)
DefPrime(59)
DefPrime(67)
DefPrime(83)
DefPrime(613)
DefPrime(631)
DefPrime(691)
DefPrime(883)
DefPrime(1009)
DefPrime(1051)
DefPrime(1201)
DefPrime(1321)
DefPrime(1723)
DefPrime(1999)
DefPrime(2671)
DefPrime(3221)
DefPrime(9539)
DefPrime(17389)

----------------------------------------------------------------------------
-- Z/mZ
----------------------------------------------------------------------------

natValI :: forall n. KnownNat n => Integer
natValI = toInteger $ natVal (Proxy @n)

-- Z/nZ
newtype Z (a :: Nat) = Z
    { unZ :: Integer
    } deriving (Eq, Ord, Enum, Generic, Hashable)
$(makeWrapped ''Z)

instance Show (Z a) where
    show (Z i) = show i

toZ :: forall n . (KnownNat n) => Integer -> Z n
toZ i = Z $ i `mod` (natValI @n)

instance (KnownNat n) => Num (Z n) where
    (Z a) + (Z b) = toZ $ a + b
    (Z a) * (Z b) = toZ $ a * b
    negate (Z 0) = Z 0
    negate (Z i) = toZ $ natValI @n - i
    fromInteger = toZ
    signum (Z a) = if a == 0 then 0 else 1
    abs = id

instance (KnownNat n) => AGroup (Z n) where
    f0 = Z 0
    (<+>) = (+)
    fneg = negate

instance (KnownNat n) => Ring (Z n) where
    f1 = Z 1
    (<*>) = (*)

instance (PrimeNat n) => Field (Z n) where
    finv (Z a) = toZ $ a `fastExp` (natValI @n - 2)

instance (PrimeNat n) => Finite (Z n) where
    allElems = map toZ $ [0..(natValI @n - 1)]
    getOrder = natValI @n

instance (PrimeNat n) => FField (Z n) where

----------------------------------------------------------------------------
-- Polynomials
----------------------------------------------------------------------------

-- | Empty polynomial is equivalent to [0]. Big endian (head is higher
-- degree coefficient).
newtype Poly a = Poly { unPoly :: [a] } deriving (Functor,Ord,Generic)

deriving instance Hashable a => Hashable (Poly a)

instance Show a => Show (Poly a) where
    show (Poly l) = "Poly " ++ show l

-- Removes zeroes from the beginning
stripZ :: (AGroup a) => Poly a -> Poly a
stripZ (Poly []) = Poly [f0]
stripZ r@(Poly [_]) = r
stripZ (Poly xs) =
    let l' = take (length xs - 1) xs
    in Poly $ dropWhile (== f0) l' ++ [L.last xs]

prettyPoly :: forall a . (Show a, Ring a) => Poly a -> String
prettyPoly (stripZ -> (Poly p)) =
    intercalate " + " $
    map mapFoo $
    filter ((/= f0) . fst) $
    reverse $ reverse p `zip` [0..]
  where
    mapFoo :: (a,Integer) -> String
    mapFoo (n,0) = show n
    mapFoo (f,1) | f == f1 = "x"
    mapFoo (f,i) | f == f1 = "x^" ++ show i
    mapFoo (n,1) = show n ++ "x"
    mapFoo (n,i) = show n ++ "x^" ++ show i

instance (AGroup a) => Eq (Poly a) where
    (==) (stripZ -> (Poly p1)) (stripZ -> (Poly p2)) = p1 == p2

deg ::  (Ring a, Integral n) => Poly a -> n
deg (stripZ -> (Poly p)) = fromIntegral $ length p - 1

applyPoly :: (FField a) => Poly a -> a -> a
applyPoly (stripZ -> (Poly p)) v =
    foldr (<+>) f0 $
        map (\(b,i) -> b <*> (v <^> (i::Integer)))
            (reverse p `zip` [0..])

-- Zips two lists adding zeroes to end of the shortest one
zip0 :: (AGroup a) => [a] -> [a] -> [(a,a)]
zip0 p1 p2 = uncurry zip sameSize
  where
    shortest | length p1 < length p2 = (p1,p2)
             | otherwise = (p2,p1)
    diff = length (snd shortest) - length (fst shortest)
    sameSize = shortest & _1 %~ ((replicate diff f0) ++)

instance (AGroup a) => AGroup (Poly a) where
    f0 = Poly [f0]
    fneg = fmap fneg
    (Poly p1) <+> (Poly p2) =
        stripZ $ Poly $ map (uncurry (<+>)) $ zip0 p1 p2

instance (Ring a) => Ring (Poly a) where
    f1 = Poly [f1]
    lhs@(Poly p1) <*> rhs@(Poly p2) =
        let acc0 :: [a]
            acc0 = replicate ((deg lhs + deg rhs)+1) f0
            withIndex :: [a] -> [(a,Int)]
            withIndex a = reverse $ reverse a `zip` [0..]

            foldFooSub :: [a] -> ((a,Int),(a,Int)) -> [a]
            foldFooSub acc ((e1,d1), (e2,d2)) =
                acc & ix (d1 + d2) %~ (<+> (e1 <*> e2))
            foldFoo :: [a] -> ((a,Int),[a]) -> [a]
            foldFoo acc ((e1,d1),el2) =
                foldl' foldFooSub acc $ map ((e1,d1),) $ withIndex el2
        in stripZ . Poly $ reverse $ foldl' foldFoo acc0 $ map (,p2) $ withIndex p1

----------------------------------------------------------------------------
-- Encoding polynomials
----------------------------------------------------------------------------

-- | Given a base and number, returns its power representation. Big
-- endian.
represent :: Integer -> Integer -> [Integer]
represent b i = reverse $ go i
  where go 0 = []
        go x = (x `mod` b) : (go $ x `div` b)

representBack :: Integer -> [Integer] -> Integer
representBack b poly = go 1 $ reverse poly
  where
    go :: Integer -> [Integer] -> Integer
    go _ []     = 0
    go i (x:xs) = (i * x) + go (i * b) xs

reflectCoeffPoly :: forall p n. (KnownNat n, KnownNat p) => Poly Integer
reflectCoeffPoly = Poly $ represent (natValI @n) (natValI @p)

getCoeffPoly :: forall p n. (KnownNat p, KnownNat n) => Poly (Z n)
getCoeffPoly = map toZ (reflectCoeffPoly @p @n)

----------------------------------------------------------------------------
-- Euclidian
----------------------------------------------------------------------------

-- | Euclidian rings.
class Ring a => Euclidian a where
    (</>) :: a -> a -> (a,a)
    -- ^ Division with (quotient,remainder)

eDiv :: Euclidian a => a -> a -> a
eDiv a b = fst $ a </> b

eMod :: Euclidian a => a -> a -> a
eMod a b = snd $ a </> b

instance Euclidian Integer where
    (</>) a b = (a `div` b, a `mod` b)

instance KnownNat n => Euclidian (Z n) where
    (</>) (Z a) (Z b) =
        let wrap = (Z . (`mod` natValI @n))
        in bimap wrap wrap (a `div` b, a `mod` b)

assert :: Bool -> Text -> a -> a
assert b str action = bool (error str) action b

-- | a / b = (quotient,remainder)
euclPoly :: (Field a) => Poly a -> Poly a -> (Poly a, Poly a)
euclPoly (stripZ -> a) (stripZ -> b@(Poly bPoly)) =
    let res@(q,r) = euclPolyGo f0 a
    in assert ((b <*> q) <+> r == a) "EuclPoly assert failed" res
  where
    euclPolyGo (stripZ -> q) (stripZ -> r)
        | (deg r :: Integer) < deg b || r == f0 = (q,r)
    euclPolyGo (stripZ -> q) (stripZ -> r@(Poly rPoly)) =
        let rDeg = deg r
            bDeg = deg b
            re = rPoly !! 0
            bd = bPoly !! 0
            x = Poly $ (re <*> (finv bd)) : replicate (rDeg - bDeg) f0
            q' = q <+> x
            r' = r <-> (x <*> b)
        in euclPolyGo q' r'

instance (Field a) => Euclidian (Poly a) where
    (</>) = euclPoly

gcdEucl :: (Euclidian a) => a -> a -> a
gcdEucl a b =
    let res = gcdEuclGo a b
    in assert (a `eMod` res == f0) "gcd doesn't divide a" $
       assert (b `eMod` res == f0) "gcd doesn't divide b" $
       res
  where
    gcdEuclGo r0 r1 =
        let r = r0 `eMod` r1
        in if r == f0 then r1 else gcdEuclGo r1 r

-- | For a,b returns (gcd,u,v) such that au + bv = gcd.
extendedEucl' :: (Euclidian n) => n -> n -> (n, n, n)
extendedEucl' a b
    | a == f0 = (b, f0, f1)
    | otherwise =
        let (g,s,t) = extendedEucl (b `eMod` a) a
        in (g, t <-> (b `eDiv` a) <*> s, s)

-- | Extended euclidian algorithm with checks.
extendedEucl :: (Euclidian n) => n -> n -> (n, n, n)
extendedEucl a b =
    let res@(g,u,v) = extendedEucl' a b in
      if | u <*> a <+> v <*> b /= g -> error "extendedEucl is broken 1"
         | a `eMod` g /= f0 -> error "extendedEucl is broken 2"
         | b `eMod` g /= f0 -> error "extendedEucl is broken 3"
         | otherwise -> res

findRoots :: forall a. (FField a) => Poly a -> [a]
findRoots x = go elems0 x
  where
    go [] _ = []
    go (e:es) p = let y = Poly [f1,f0] <-> Poly [e]
                      (q,r) = p </> y
                  in if r == f0 then e : go (e:es) q else go es p
    elems0 = allElems @a

-- | Class for polynomials that can serve as finite poly field
-- limiters. For instance,
class (KnownNat p, KnownNat n) => PolyDivisor p n where
    pdMod :: Poly (Z n) -> Poly (Z n)

instance {-# OVERLAPPABLE #-}  (KnownNat p, PrimeNat n) => PolyDivisor p n where
    pdMod x = x `eMod` (getCoeffPoly @p @n)

----------------------------------------------------------------------------
-- Convolution polynomials (and rings)!
----------------------------------------------------------------------------

-- Returns the N from the encoded poly or fails.
representConv :: forall q. KnownNat q => Integer -> Int
representConv p =
    if not correctPoly
    then error "representConv failed: incorrect poly"
    else length y - 1
  where
    y = represent (natValI @q) p
    correctPoly =
        L.head y == 1 &&
        all (== 0) (take (length y - 2) $ L.tail y) &&
        L.last y == natValI @q - 1

-- Convert N in base (Z q) to encoding of x^N - 1
representBackConv :: forall q. KnownNat q => Int -> Integer
representBackConv n = representBack (natValI @q) poly
  where
    poly = 1 : replicate (n - 1) 0 ++ [natValI @q - 1]

replaceConv :: forall q f. (KnownNat q, KnownNat f) => Poly (Z f) -> Poly (Z f)
replaceConv x = res
  where
    res = replaceAll x
    -- N
    n = representConv @f (natValI @q)
    replaceAll z0@(Poly z) =
        let headCoeff = deg z0
        in if headCoeff < n then z0
           else replaceAll $ stripZ $ Poly $ L.tail (z & ix n %~ (<+> L.head z))


instance {-# OVERLAPS #-} PolyDivisor 33 2 where pdMod = replaceConv @33
instance {-# OVERLAPS #-} PolyDivisor 245 3 where pdMod = replaceConv @245
instance {-# OVERLAPS #-} PolyDivisor 177149 3 where pdMod = replaceConv @177149
instance {-# OVERLAPS #-} PolyDivisor 1027 4 where pdMod = replaceConv @1027
instance {-# OVERLAPS #-} PolyDivisor 349 7 where pdMod = replaceConv @349
instance {-# OVERLAPS #-} PolyDivisor 2189 7 where pdMod = replaceConv @2189
instance {-# OVERLAPS #-} PolyDivisor 1048591 16 where pdMod = replaceConv @1048591
instance {-# OVERLAPS #-} PolyDivisor 3404825469 23 where pdMod = replaceConv @3404825469
instance {-# OVERLAPS #-} PolyDivisor 194754273921 41 where pdMod = replaceConv @194754273921
instance {-# OVERLAPS #-} PolyDivisor 34359738495 128 where pdMod = replaceConv @34359738495
instance {-# OVERLAPS #-} PolyDivisor 122130132904968017149 67 where pdMod = replaceConv @122130132904968017149
instance {-# OVERLAPS #-} PolyDivisor 2910383045673370361331249 3125 where pdMod = replaceConv @2910383045673370361331249


----------------------------------------------------------------------------
-- Polynomials quotieng rings/fields
----------------------------------------------------------------------------

-- Empty polynomial is equivalent for [0]. Head -- higher degree.
newtype FinPoly (p :: Nat) a = FinPoly { unFinPoly :: Poly a } deriving (Eq,Ord,Generic)

deriving instance Hashable (Poly a) => Hashable (FinPoly p a)

type FinPolyZ p n = FinPoly p (Z n)

instance (Show a) => Show (FinPoly p a) where
    show (FinPoly x) = "Fin" <> show x

allFinPolys :: forall p n. (KnownNat p, KnownNat n) => [FinPoly p (Z n)]
allFinPolys = map (FinPoly . stripZ . Poly . (map toZ)) $ binGen s
  where
    b :: Integer
    b = fromIntegral $ natValI @n
    s :: Integer
    s = deg (reflectCoeffPoly @p @n)
    binGen :: Integer -> [[Integer]]
    binGen 0 = [[]]
    binGen n =
        let x = binGen (n-1)
        in mconcat $ map (\i -> map (i :) x) [0..b-1]

isPrimePoly :: forall n . (KnownNat n, Euclidian (Poly (Z n))) => Poly (Z n) -> Bool
isPrimePoly p@(Poly pP) =
    let i = representBack (natValI @n) (map unZ pP)
        lesspolys :: [Poly (Z n)]
        lesspolys = map (Poly . map toZ . represent (natValI @n)) [2..(i-1)]
    in all (\pl -> p `eMod` pl /= f0) lesspolys

mkFinPoly :: forall p n . PolyDivisor p n => Poly (Z n) -> FinPoly p (Z n)
mkFinPoly x = FinPoly $ pdMod @p (stripZ x)

type FinPolyNats p n = (KnownNat p, PrimeNat n)

--instance (FinPolyNats p n) => AGroup (FinPoly p (Z n)) where
instance PolyDivisor p n => AGroup (FinPoly p (Z n)) where
    f0 = mkFinPoly f0
    (<+>) (FinPoly p1) (FinPoly p2) = mkFinPoly (p1 <+> p2)
    fneg (FinPoly p1) = mkFinPoly $ (getCoeffPoly @p) <-> p1

instance PolyDivisor p n => Ring (FinPoly p (Z n)) where
    f1 = mkFinPoly f1
    (<*>) (FinPoly p1) (FinPoly p2) = mkFinPoly (p1 <*> p2)

instance (PolyDivisor p n, PrimeNat n) => Euclidian (FinPoly p (Z n)) where
    (</>) (FinPoly p1) (FinPoly p2) = let (q,r) = p1 </> p2 in (mkFinPoly q, mkFinPoly r)

class FinPolyNats p n => PrimePoly (p :: Nat) (n :: Nat) where

-- 19 = x^4 + x + 1 is prime poly over F_2
instance PrimePoly 19 2
-- 67 = x^6 + x + 1 is prime poly over F_2
instance PrimePoly 67 2
-- 75 = x^6 + x^3 + x + 1 is NOT prime
-- 11 = x^3 + x + 1 is prime poly over F_2
instance PrimePoly 11 2
-- ℂ: x^2 + 1 for p = 3 (mod 4)
instance PrimePoly 362 19
instance PrimePoly 2210 47
instance PrimePoly 477482 691
instance PrimePoly 2968730 1723

instance (PolyDivisor p n) => Finite (FinPoly p (Z n)) where
    allElems = allFinPolys
    getOrder =
        let b = fromIntegral (natValI @n) :: Integer
            s = deg (reflectCoeffPoly @p @n) :: Integer
        in (b ^ s)

-- Technically we can call invFinPolyFermat with just a PolyDivisor
-- constraint, but the algorithm will fail (fermat's inv works only
-- for irreducable elems), so we require p to be prime.
instance (PrimePoly p n) => Field (FinPoly p (Z n)) where
    finv = fermatInverse

instance (PrimePoly p n) => FField (FinPoly p (Z n)) where

irreducablePoly :: forall n. (PrimeNat n) => Integer -> Poly (Z n) -> Bool
irreducablePoly d (stripZ -> a) =
    let n = natValI @n
        l = representBack n $ 1 : replicate (fromIntegral d) 0
        ps = drop (fromIntegral n) $ (map (stripZ . Poly . map (toZ @n) . represent n) [0..(l-1)])
    in all (\x -> a `eMod` x /= f0) ps

invPolyEuclidian ::
       forall p n. (PrimeNat n, PolyDivisor p n)
    => FinPolyZ p n
    -> Maybe (FinPolyZ p n)
invPolyEuclidian x = do
    -- Polynomial GCD is not unique.
    -- https://en.wikipedia.org/wiki/Polynomial_greatest_common_divisor
    let (g,u,_) = extendedEucl (unFinPoly x) (getCoeffPoly @p)
    guard (deg g == (0 :: Integer))
    let Poly [g'] = g
    let res = mkFinPoly (map (<*> finv g') u)
    when (res <*> x /= f1) $ error "invPolyEuclidian is broken"
    pure res

----------------------------------------------------------------------------
-- TODO Move to test modules
----------------------------------------------------------------------------

_testFinPolys :: IO ()
_testFinPolys = do
    let pPoly = [1,0,0,1,1]
    let pEnc = representBack 2 pPoly
    let (x :: FinPoly 19 (Z 2)) = mkFinPoly (Poly [1,0])
    let z = x <^> 12
    let y = finv z
    print pEnc
    print $ z
    print $ y
    print $ z <*> y



_testGenerators :: IO ()
_testGenerators = do
    print $ getGen @(Z 17)
    let (g :: Poly (Z 2)) = Poly [1,1,1]
    print g
    print (finv (Z 1 :: Z 2))
    let h = Poly [1,1]
    print h
    print $ g `euclPoly` h
    print $ take 20 $ iterate (<*> g) g
    print (allFinPolys :: [FinPoly 19 (Z 2)])
    print $ getGen @(FinPoly 19 (Z 2))
    print $ getOrder @(FinPoly 19 (Z 2))
    print $ allFinPolys @75 @2

_testPrimality :: IO ()
_testPrimality = do
    print $ isPrimePoly $ (Poly [1,0,0,1,1] :: Poly (Z 2))
    print $ isPrimePoly $ (Poly [1,1,1] :: Poly (Z 2))
    print $ isPrimePoly $ (Poly [1,0,1,1] :: Poly (Z 2))
    print $ isPrimePoly $ (Poly [1,0,1,1] :: Poly (Z 2))
    print $ isPrimePoly $ (Poly [1,0,0,0,1,1,1,0,1] :: Poly (Z 2))
    print $ (Poly (map toZ $ represent 2 67) :: Poly (Z 2))
    print $ isPrimePoly $ (Poly (map toZ $ represent 2 75) :: Poly (Z 2))
    print $ isPrimePoly $ (Poly (map toZ $ represent 2 57) :: Poly (Z 2))
    print $ isPrimePoly $ (Poly (map toZ $ represent 2 67) :: Poly (Z 2))
    print $ isPrimePoly $ (Poly (map toZ $ represent 2 51) :: Poly (Z 2))
