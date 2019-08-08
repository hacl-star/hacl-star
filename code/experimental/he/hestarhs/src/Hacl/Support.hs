-- | Methods to support PAHE, like key generation, packing modes, etc.

module Hacl.Support where

import Universum hiding (exp, last, (<*>))

import Data.List (splitAt, (!!))
import Numeric (log)
import System.IO.Unsafe (unsafePerformIO)
import System.Random (randomIO, randomRIO)

import Hacl.Bignum
import Hacl.Raw
import Lib hiding (crt)
import Utils


-- number of MR iterations given the number of limbs
-- from openssl BN_prime_checks_for_size
mrIters :: Word32 -> Word32
mrIters lm =
    if lm >= 55 then 3 else
    if lm >= 21 then 4 else
    if lm >= 7 then 5 else
    if lm >= 5 then 8 else
    if lm >= 1 then 27 else
    40

testPrime :: Integer -> IO Bool
testPrime i = do
    (p,sz) <- toBignumExact i
    r <- bnIsPrime sz 0 p
    freeBignum p
    pure $ r == 1

-- testPrime 10635024147909566416140599671674429005755303252598161859729148401199127240856978988690173740916103428272796028915327183568661188513792102349407973645274345
compareToMR :: IO ()
compareToMR = replicateM_ 10000 $ do
    x <- randomRIO (0,2^(1024::Integer))
    b1 <- testPrime x
    let b2 = isPrimeMR 40 x
    when (b1 /= b2) $ error $
        "Mismatch: " <> show x <> " " <> show (b1,b2)

-- https://stackoverflow.com/questions/6325576/how-many-iterations-of-rabin-miller-should-i-use-for-cryptographic-safe-primes
genPrime :: Int -> IO Integer
genPrime bits = do
    p <- randomRIO (2 ^ (bits - 4),2 ^ bits) `suchThat` odd
    b <- testPrime p
    if b then pure p else genPrime bits

legendreSymbol :: Integer -> Integer -> Integer
legendreSymbol p a = let res = exp p a ((p-1) `div` 2) in if res == p-1 then (-1) else res

boolToInt :: Bool -> Int
boolToInt = bool 0 1

intToBool = (== 1) . (`mod` 2)

genDataGM :: Int -> IO (Integer,Integer,Integer,Integer,Bool,Bool)
genDataGM bits = do
    let genPrimes = do
            p <- genPrime (bits `div` 2)
            q <- genPrime (bits `div` 2)
            if p == q then genPrimes else pure (p,q)
    (p,q) <- genPrimes
    let n = p * q
    let genY = do
            y <- randomRIO (2^(bits-2), n-1)
            if legendreSymbol p y == -1 && legendreSymbol q y == -1
               then pure y
               else genY
    y <- genY
    let genR = do
            r <- randomRIO (2^(bits-2), n-1)
            if (r * r) `mod` n > 0 && (r * r * y) `mod` n > 0 then pure r else genR
    r <- genR
    m1 <- randomIO
    m2 <- randomIO
    return (p,q,y,r,m1,m2)


genDataPaillier :: Int -> IO (Integer,Integer,Integer,Integer,Integer)
genDataPaillier bits = do
    let genPrimes = do
            p <- genPrime (bits `div` 2)
            q <- genPrime (bits `div` 2)
            if p == q then genPrimes else pure (p,q)
    (p,q) <- genPrimes
    let n = p * q
    let genR = do
            r <- randomRIO (0,n-1)
            if gcd r n == 1 then pure r else genR
    r <- genR
    m1 <- randomRIO (0,n-1)
    m2 <- randomRIO (0,n-1)
    return (p,q,r,m1,m2)


log2 :: Integer -> Integer
log2 x = ceiling $ log (fromIntegral (x+1)) / log 2

fromFacts :: [(Integer,Integer)] -> Integer
fromFacts = product . map (\(p,i) -> p ^ i)

recombineFacts :: [(Integer,Integer)] -> [(Integer,Integer)]
recombineFacts xs =
    let ps = ordNub $ map fst xs in
    map (\p -> (p,sum $ map snd $ filter ((== p). fst) xs)) ps

flattenFacts :: [(Integer,Integer)] -> [Integer]
flattenFacts = concatMap (\(p,j) -> replicate (fromIntegral j) p)

factToOrders :: [(Integer,Integer)] -> [Integer]
factToOrders facts  =
    sort $ ordNub $ map product $ allCombinations $ flattenFacts facts

orderFact :: [Integer] -> Integer -> Integer -> Integer
orderFact possibleOrders n g =
    fromMaybe (error "can't be") $ find (\o -> exp n g o == 1) $ sort possibleOrders

fastFindOrder :: Integer -> Integer -> [Integer] -> IO Integer
fastFindOrder n g flatFactors = do

    let loop extraPrms = do
            if extraPrms == [] then pure []
            else do
                let extraPrmsProd = product extraPrms
                resIndex <-
                    findM (\i -> pure $ exp n g (extraPrmsProd `div` (extraPrms !! i)) == 1)
                          [0..length extraPrms-1]
                case resIndex of
                    Nothing -> pure extraPrms
                    Just i  -> loop (listRem extraPrms i)

    product <$> loop flatFactors
  where
    listRem ls i = let (ls1,ls2) = splitAt i ls in ls1 ++ drop 1 ls2

findWithOrder :: Integer -> Integer -> Integer -> [Integer] -> Integer -> IO Integer
findWithOrder p q n (sort -> posOrders) reqO = do
    let bn = fromIntegral $ log2 n

    bnZero <- toBignum bn 0
    bnOne <- toBignum bn 1
    p' <- toBignum bn p
    q' <- toBignum bn q
    n' <- toBignum bn n
    reqO' <- toBignum bn reqO
    posOrders' <- mapM (toBignum bn) posOrders

    -- openssl version must be faster
    let randomBignum = toBignum bn =<< randomRIO (0,n-1)

    e <- toBignum bn 0
    let orderFactBN :: Bignum -> Bignum -> IO Bignum
        orderFactBN modulo g =
            fromMaybe (error "can't be") <$>
            findM (\o -> do
                        bnModExp bn bn modulo g o e
                        bnIsEqual bn bn e bnOne)
            posOrders'


    rem1 <- toBignum bn 0
    oDivReqo <- toBignum bn 0
    oModReqo <- toBignum bn 0 -- not used
    cand <- toBignum bn 0
    candModP <- toBignum bn 0
    candModQ <- toBignum bn 0
    let go i = do
            g <- randomBignum
            o <- orderFactBN n' g
            bnRemainder bn bn o reqO' rem1
            cond1 <- bnIsEqual bn bn rem1 bnZero
            if cond1 then do
                bnDivide bn o reqO' oDivReqo oModReqo
                bnModExp bn bn n' g oDivReqo cand -- cand = g^(
                bnRemainder bn bn cand p' candModP
                bnRemainder bn bn cand q' candModQ
                o1 <- orderFactBN p' candModP
                o2 <- orderFactBN q' candModQ

                b1 <- bnIsEqual bn bn o1 o2
                b2 <- bnIsEqual bn bn o1 reqO'
                if b1 && b2 then pure cand
                else go (i+1)
            else go (i+1)

    fromBignum bn =<< go 0

genDataDGK ::
       [(Integer, Integer)]
    -> Int
    -> IO (Integer, Integer, Integer, Integer, Integer, Integer)
genDataDGK uFacts bits = do
    let u = fromFacts uFacts
    let vbits = 160
    let ubits = fromIntegral $ log2 u
    let rbits = bits `div` 2 - ubits - vbits
    when (rbits < 0) $ error $ "genDataDGK: incorrect params: " <> show (vbits, ubits, rbits)

    v <- genPrime vbits
    let genR (i::Integer) = do
          r <- genPrime rbits
          let p = 2 * u * v * r + 1
          b <- testPrime p
          if b then pure (r,p) else genR (i+1)

    putTextLn "Generating p"
    (r_p,p) <- genR 0
    putTextLn "Generating q"
    (r_q,q) <- genR 0
    when (p == q) $ error "p = q"
    let n = p * q
    putTextLn "Generated n"

    let phinFacts =
            recombineFacts $
            [(2,2),(r_p,1),(r_q,1),(v,2)] <> uFacts <> uFacts
    unless (fromFacts phinFacts == (p-1)*(q-1)) $ error "er2"
    let flatFacts = flattenFacts phinFacts

    let findWithOrd reqO = do
            g <- randomRIO (0, (p-1)*(q-1))
            o <- fastFindOrder n g flatFacts
            putTextLn "Testing order"
            if o `mod` reqO == 0 then do
                let cand = exp n g (o `div` reqO)
                o1 <- fastFindOrder p (cand `mod` p) flatFacts
                o2 <- fastFindOrder q (cand `mod` q) flatFacts
                if o1 == o2 && o1 == reqO then pure cand
                else findWithOrd reqO
            else findWithOrd reqO

    putTextLn "Generating g"
    g <- findWithOrd (u * v)
    putTextLn "Generating h"
    h <- findWithOrd v

    pure (p,q,u,v,g,h)

genConsecutivePrms :: Int -> Integer -> [Integer]
genConsecutivePrms n bound =
    reverse $ go 0 [] (if even bound then bound+1 else bound+2)
  where
    go l xs toTest = if l >= n then xs else
        if isPrimeMR 40 toTest
        then go (l+1) (toTest:xs) (toTest+2)
        else go l xs (toTest+2)

genDataDGKWithPrimes ::
       Int
    -> Integer
    -> Int
    -> IO ([Integer], Integer, Integer, Integer, Integer, Integer, Integer)
genDataDGKWithPrimes primeN primeBound bits = do
    let prms = genConsecutivePrms primeN primeBound
    let ulog = sum $ map log2 prms
    (p,q,u,v,g,h) <- genDataDGK (map (,1) prms) bits
    pure (prms,p,q,u,v,g,h)

dgkKeyGenLookup ::
       Int
    -> Integer
    -> Int
    -> Maybe ([Integer], Integer, Integer, Integer, Integer, Integer, Integer)
-- genDataDGKWithPrimes 2 (2^20) 700
dgkKeyGenLookup 1 256 1024 = Just $
    ([257],3732214783585243587731814718439986466845741344534796423985883655101507502552257988799973695582599164697611520206109374219741659192024665020131494674692327,8369472600970571433517067531920388416733309870274033491930263977735081762442935404116624004417679070558022165132539981470520487590705417510088710858291379,257,1403523604213918558808289054955896504492641011577,13030354969303630969733778964373077938733223278464478719638209219455430696276900568533879925630320849706088119606920757256486418731413074990963761014390179999356919722964240368868311000430758308187981928130857842009268435495648513182865883163857274452196151449670103442425704828872561803693281560300196681261,6019263928252908907161142396421309020027671385288174913805494713269152697528590136442342739843371442026085712316916011360422672098423538680011609756568291926274581149793537063741319223638278173225699669656764670688632120291667871158805680480598806747490949014916784679525324712609232919778308691450252578911)
dgkKeyGenLookup 8 256 1024 = Just $
    ([257,263,269,271,277,281,283,293],306572305583672616744239395448668594894172318656992241432836770474340616788664010142145577935907735628238669042809487298608761873954247733306341677793259,584759951194268865068850601459598653333289539063858165228790865006098883255241344513252068893178673999949272256060298276878257093614595515246823667464599,31801718393038504727,181620239505579549639566527848545665303877356001,71656103712823701247220977997945811537445459797299164703301916146600087729249397639310839074754102244006218711428655779458468220419898150620225170131114738912026671179739402388023666966769056453238521894127586649799585436772541482710909230371574615526172314610279155962133228704545503423017007814716718007,81501054765793724573864517217313041297845190317180790806611517582983435841599065713426180046118005659468589731448924073201097488427773288309516709190393266307539047490815932438766944388575134762208683248779550145510334643885113311753726468126706162817392059902600165092334486773132159879695737239010607600)
dgkKeyGenLookup 1 1024 1024 = Just $
    ([1031],819467478441409578680565215809659140399513637928427518890619328920513556838761162880342002642266514012910252161940647676165878215023637240526715914911283,3093872912383766732302296645294018303483671398886126764461912741097425032097938496804903044022456070873114625221104963712278151614356040143341618128922379,1031,423677040528389857288717782838004225915497386559,2017254870777724050351559686368058286413981531673486392807675789692664479567430125918204115651412189331505202617864206984251533799960856235745396202515839096864618858057422321862438859577672160833609381763971814888238525740489902364049351306059451684875364805549841848593787444281465200528065225156914826800,1753496204512772664099930132463047151360615957767587261675940905094852063066429236470049618691164484350247075043416212224714390588162404105751208150328916782725742054915439135146851100154838197879010378007776713942576510370191786923832587552385196204198184292537995043048262084014931392330589198335497543895)
dgkKeyGenLookup 2 1048576 700 = Just $
    ([1048583,1048589],1895089596695635987044392085844392979345094436303371616593800702072823833377343780663139692699220309214467,1233650831883099230153849542876191261913580924454571036409560025644937233018208400997158133586030949795059,1099532599387,1426476897108638371825766716642800048506732913643,1656538870108677916077033972037100235170746303410383531631175515688417525915790037496147585782798401746528225873757261702451073191397227907472359036081702994394585493896112852303850272946094029353544515902429963,1109134116557813645666153083598642098863534434376690627045137653790218908038050002143975865840590196552485698017229738578393420525943325790374596246808527264216261339249706287872874469197014263981049460345253999)
dgkKeyGenLookup _ _ _ = Nothing



dgkKeyGenWithLookup ::
       Int
    -> Integer
    -> Int
    -> IO ([Integer], Integer, Integer, Integer, Integer, Integer, Integer)
dgkKeyGenWithLookup primeN primeBound bits =
    case dgkKeyGenLookup primeN primeBound bits of
        Just x -> pure x
        Nothing -> do
          res <- genDataDGKWithPrimes primeN primeBound bits
          print (primeN,primeBound,bits)
          print res
          pure res
