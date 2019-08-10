-- | Permutation + fold protocol.

module PermuteFold
    ( permuteFoldClient
    , permuteFoldServer
    ) where

import Universum

import Data.List (findIndex, (!!))
import qualified Data.List.NonEmpty as NE
import System.Random (randomRIO)
import System.ZMQ4

import Hacl
import Utils

-- Permutes list of 2k elements (passed as 2 ciphertexts) into 2
-- another ciphertexts.
--
-- it computes the inverse perm.
permuteFoldClient ::
       Pahe sTop
    => Socket Req
    -> PahePk sTop
    -> Int
    -> [Int]
    -> PaheCiph sTop
    -> PaheCiph sTop
    -> IO (PaheCiph sTop, PaheCiph sTop)
permuteFoldClient sock pk l perm v1 v2 = do
    let k = paheK pk
    let k2 = k `div` 2
    when (k2 * 2 /= k) $ error "permuteFoldClient doesn't support non-even k"

    let perminv = map (\j ->fromMaybe (error "permuteClient perminv") $
                        findIndex (==j) perm) [0..2*k-1]

    mask1Raw <- replicateM k $ randomRIO (0, 2 ^ (l + lambda) - 1)
    mask2Raw <- replicateM k $ randomRIO (0, 2 ^ (l + lambda) - 1)
    mask1Enc <- paheEnc pk mask1Raw
    mask2Enc <- paheEnc pk mask2Raw
    v1Masked <- paheSIMDAdd pk v1 mask1Enc
    v2Masked <- paheSIMDAdd pk v2 mask2Enc

    sendMulti sock =<< NE.fromList <$> mapM (paheToBS pk) [v1Masked,v2Masked]

    -- k ciphertexts containing valuesMasked_i in all slots
    replElems <- mapM (paheFromBS pk) =<< receiveMulti sock

    let loop w j = if j == k then pure (paheZero pk) else do
            next <- loop w (j+1)
            let i = perminv !! (w+j)
            -- We select jth element from (perm^-1 j)
            let selMask = replicate j 0 ++ [1] ++ replicate (k - j - 1) 0
            cur <- paheSIMDMulScal pk (replElems !! i) selMask
            paheSIMDAdd pk cur next

    permuted1 <- loop 0 0
    permuted2 <- loop k 0

    let permutedMaskNeg = map (\i -> negate ((mask1Raw++mask2Raw) !! (perminv !! i))) [0..2*k-1]
    let m1 = take k permutedMaskNeg
    let m2 = drop k permutedMaskNeg

    r1 <- paheSIMDAdd pk permuted1 =<< paheEnc pk m1
    r2 <- paheSIMDAdd pk permuted2 =<< paheEnc pk m2

    pure (r1,r2)

permuteFoldServer ::
       Pahe sTop
    => Socket Rep
    -> PaheSk sTop
    -> IO ()
permuteFoldServer sock sk = do
    let pk = paheToPublic sk
    [p1,p2] <- mapM (paheDec sk <=< paheFromBS pk) =<< receiveMulti sock
    let dups = map (\e -> replicate (paheK pk) e) $ p1 ++ p2
    encDups <- mapM (paheEnc pk) dups
    sendMulti sock =<< (NE.fromList <$> mapM (paheToBS pk) encDups)
