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

    , findGenerator

    , natValI
    , Z (..)
    , toZ
    , PrimeNat
    , Poly(..)
    , stripZ
    , prettyPoly
    , deg
    , applyPoly
    ) where

import qualified Prelude
import Universum hiding (head, (<*>))

import Control.Lens (ix, makeWrapped)
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
