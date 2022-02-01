module Hacl.P256

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence

open FStar.Mul
open Spec.P256
open Spec.P256.Lemmas
open Spec.P256.Definitions
open Spec.Hash.Definitions

open Spec.DH
open Spec.ECDSAP256.Definition
open Hacl.Impl.P256.Compression
open Spec.P256.MontgomeryMultiplication

[@@ CPrologue "
/*******************************************************************************

ECDSA and ECDH functions over the P-256 NIST curve.

This module implements signing and verification, key validation, conversions
between various point representations, and ECDH key agreement.

*******************************************************************************/

/**************/
/* Signatures */
/**************/

/*
  The standard strongly encourages the user to hash the input before signing
  it. Therefore, we recommend using one of the signature variants below.
*/";

Comment "Combined SHA2-256 and P256 signature function.

Input: result buffer: uint8[64], \n m buffer: uint8 [mLen], \n priv(ate)Key: uint8[32], \n k (nonce): uint32[32]. 
  \n Output: bool, where True stands for the correct signature generation. False value means that an error has occurred. 
  \n The private key and the nonce are expected to be more than 0 and less than the curve order."]
val ecdsa_sign_p256_sha2: result: lbuffer uint8 (size 64) 
  -> mLen: size_t 
  -> m: lbuffer uint8 mLen 
  -> privKey: lbuffer uint8 (size 32) 
  -> k: lbuffer uint8 (size 32) -> 
  Stack bool
  (requires fun h -> 
    live h result /\ live h m /\ live h privKey /\ live h k /\
    disjoint result m /\
    disjoint result privKey /\
    disjoint result k /\
    nat_from_bytes_be (as_seq h privKey) > 0 /\
    nat_from_bytes_be (as_seq h k) > 0 /\
    nat_from_bytes_be (as_seq h privKey) < prime_p256_order /\
    nat_from_bytes_be (as_seq h k) < prime_p256_order
  )
  (ensures fun h0 flag h1 -> 
    modifies (loc result) h0 h1 /\
     (assert_norm (pow2 32 < pow2 61);
      let resultR = gsub result (size 0) (size 32) in 
      let resultS = gsub result (size 32) (size 32) in 
      let r, s, flagSpec = Spec.ECDSA.ecdsa_signature_agile (Spec.ECDSA.Hash SHA2_256) (uint_v mLen) (as_seq h0 m) (as_seq h0 privKey) (as_seq h0 k) in 
      as_seq h1 resultR == nat_to_bytes_be 32 r /\
      as_seq h1 resultS == nat_to_bytes_be 32 s /\
      flag == flagSpec 
    )    
  )


[@ (Comment "Combined SHA2-384 and P256 signature function.

Input: result buffer: uint8[64], \n m buffer: uint8 [mLen], \n priv(ate)Key: uint8[32], \n k (nonce): uint32[32]. 
  \n Output: bool, where True stands for the correct signature generation. False value means that an error has occurred. 
  \n The private key and the nonce are expected to be more than 0 and less than the curve order.")]
val ecdsa_sign_p256_sha384: result: lbuffer uint8 (size 64) -> mLen: size_t -> m: lbuffer uint8 mLen ->
  privKey: lbuffer uint8 (size 32) -> 
  k: lbuffer uint8 (size 32) -> 
  Stack bool
  (requires fun h -> 
    live h result /\ live h m /\ live h privKey /\ live h k /\
    disjoint result m /\
    disjoint result privKey /\
    disjoint result k /\
    nat_from_bytes_be (as_seq h privKey) > 0 /\
    nat_from_bytes_be (as_seq h k) > 0 /\
    nat_from_bytes_be (as_seq h privKey) < prime_p256_order /\
    nat_from_bytes_be (as_seq h k) < prime_p256_order
  )
  (ensures fun h0 flag h1 -> 
    modifies (loc result) h0 h1 /\
     (assert_norm (pow2 32 < pow2 61);
      let resultR = gsub result (size 0) (size 32) in 
      let resultS = gsub result (size 32) (size 32) in 
      let r, s, flagSpec = Spec.ECDSA.ecdsa_signature_agile (Spec.ECDSA.Hash SHA2_384) (uint_v mLen) (as_seq h0 m) (as_seq h0 privKey) (as_seq h0 k) in 
      as_seq h1 resultR == nat_to_bytes_be 32 r /\
      as_seq h1 resultS == nat_to_bytes_be 32 s /\
      flag == flagSpec 
    )    
  )


[@ (Comment "Combined SHA2-512 and P256 signature function.

Input: result buffer: uint8[64], \n m buffer: uint8 [mLen], \n priv(ate)Key: uint8[32], \n k (nonce): uint32[32]. 
  \n Output: bool, where True stands for the correct signature generation. False value means that an error has occurred. 
  \n The private key and the nonce are expected to be more than 0 and less than the curve order.")]
val ecdsa_sign_p256_sha512: result: lbuffer uint8 (size 64) 
  -> mLen: size_t 
  -> m: lbuffer uint8 mLen 
  -> privKey: lbuffer uint8 (size 32) 
  -> k: lbuffer uint8 (size 32) -> 
  Stack bool
  (requires fun h -> 
    live h result /\ live h m /\ live h privKey /\ live h k /\
    disjoint result m /\
    disjoint result privKey /\
    disjoint result k /\
    nat_from_bytes_be (as_seq h privKey) > 0 /\
    nat_from_bytes_be (as_seq h k) > 0 /\
    nat_from_bytes_be (as_seq h privKey) < prime_p256_order /\
    nat_from_bytes_be (as_seq h k) < prime_p256_order
  )
  (ensures fun h0 flag h1 -> 
    modifies (loc result) h0 h1 /\
     (assert_norm (pow2 32 < pow2 61);
      let resultR = gsub result (size 0) (size 32) in 
      let resultS = gsub result (size 32) (size 32) in 
      let r, s, flagSpec = Spec.ECDSA.ecdsa_signature_agile (Spec.ECDSA.Hash SHA2_512) (uint_v mLen) (as_seq h0 m) (as_seq h0 privKey) (as_seq h0 k) in 
      as_seq h1 resultR == nat_to_bytes_be 32 r /\
      as_seq h1 resultS == nat_to_bytes_be 32 s /\
      flag == flagSpec 
    )    
  )


[@ (Comment "P256 signature WITHOUT hashing.

This is NOT RECOMMENDED. Please use of the combined hash-and-sign functions
above.

The argument `m` MUST be at least 32 bytes (i.e. `mLen >= 32`).

NOTE: The equivalent functions in OpenSSL and Fiat-Crypto both accept inputs
smaller than 32 bytes. These libraries left-pad the input with enough zeroes to
reach the minimum 32 byte size. Clients who need behavior identical to OpenSSL
need to perform the left-padding themselves.

Input: result buffer: uint8[64], \n m buffer: uint8 [mLen], \n priv(ate)Key: uint8[32], \n k (nonce): uint32[32]. 
  \n Output: bool, where True stands for the correct signature generation. False value means that an error has occurred. 
  \n The private key and the nonce are expected to be more than 0 and less than the curve order.
  \n The message m is expected to be hashed by a strong hash function, the lenght of the message is expected to be 32 bytes and more.")]
val ecdsa_sign_p256_without_hash: result: lbuffer uint8 (size 64) 
  -> mLen: size_t {uint_v mLen >= Spec.ECDSA.min_input_length Spec.ECDSA.NoHash}
  -> m: lbuffer uint8 mLen
  -> privKey: lbuffer uint8 (size 32) 
  -> k: lbuffer uint8 (size 32) -> 
  Stack bool
  (requires fun h -> 
    live h result /\ live h m /\ live h privKey /\ live h k /\
    disjoint result m /\
    disjoint result privKey /\
    disjoint result k /\
    nat_from_bytes_be (as_seq h privKey) > 0 /\
    nat_from_bytes_be (as_seq h k) > 0 /\
    nat_from_bytes_be (as_seq h privKey) < prime_p256_order /\
    nat_from_bytes_be (as_seq h k) < prime_p256_order
  )
  (ensures fun h0 flag h1 -> 
    modifies (loc result) h0 h1 /\
     (assert_norm (pow2 32 < pow2 61);
      let resultR = gsub result (size 0) (size 32) in 
      let resultS = gsub result (size 32) (size 32) in 
      let r, s, flagSpec = Spec.ECDSA.ecdsa_signature_agile Spec.ECDSA.NoHash (uint_v mLen) (as_seq h0 m) (as_seq h0 privKey) (as_seq h0 k) in  
      as_seq h1 resultR == nat_to_bytes_be 32 r /\
      as_seq h1 resultS == nat_to_bytes_be 32 s /\
      flag == flagSpec 
    )    
  )


[@@ CPrologue "
/****************/
/* Verification */
/****************/

/*
  The user MUST validate the public key using `verify_q` before calling any of the
  verification functions.
*/
";

(Comment " The input of the function is considered to be public, 
  thus this code is not secret independent with respect to the operations done over the input.
  \n Input: m buffer: uint8 [mLen], \n pub(lic)Key: uint8[64], \n r: uint8[32], \n s: uint8[32]. 
  \n Output: bool, where true stands for the correct signature verification. ")]
val ecdsa_verif_p256_sha2:
    mLen: size_t
  -> m: lbuffer uint8 mLen
  -> pubKey: lbuffer uint8 (size 64)
  -> r: lbuffer uint8 (size 32)
  -> s: lbuffer uint8 (size 32) ->
   Stack bool
    (requires fun h -> live h pubKey /\ live h r /\ live h s /\ live h m)
    (ensures fun h0 result h1 ->
      assert_norm (pow2 32 < pow2 61); 
      let publicKeyX = nat_from_bytes_be (as_seq h1 (gsub pubKey (size 0) (size 32))) in
      let publicKeyY = nat_from_bytes_be (as_seq h1 (gsub pubKey (size 32) (size 32))) in
      let r = nat_from_bytes_be (as_seq h1 r) in
      let s = nat_from_bytes_be (as_seq h1 s) in
      modifies0 h0 h1 /\
      result == Spec.ECDSA.ecdsa_verification_agile (Spec.ECDSA.Hash SHA2_256) (publicKeyX, publicKeyY) r s (v mLen) (as_seq h0 m)
    )


[@ (Comment "  The input of the function is considered to be public, 
  thus this code is not secret independent with respect to the operations done over the input.
  \n Input: m buffer: uint8 [mLen], \n pub(lic)Key: uint8[64], \n r: uint8[32], \n s: uint8[32]. 
  \n Output: bool, where true stands for the correct signature verification. ")]
val ecdsa_verif_p256_sha384:
    mLen: size_t
  -> m: lbuffer uint8 mLen
  -> pubKey: lbuffer uint8 (size 64)
  -> r: lbuffer uint8 (size 32)
  -> s: lbuffer uint8 (size 32) ->
   Stack bool
    (requires fun h -> live h pubKey /\ live h r /\ live h s /\ live h m)
    (ensures fun h0 result h1 ->
      assert_norm (pow2 32 < pow2 61); 
      let publicKeyX = nat_from_bytes_be (as_seq h1 (gsub pubKey (size 0) (size 32))) in
      let publicKeyY = nat_from_bytes_be (as_seq h1 (gsub pubKey (size 32) (size 32))) in
      let r = nat_from_bytes_be (as_seq h1 r) in
      let s = nat_from_bytes_be (as_seq h1 s) in
      modifies0 h0 h1 /\
      result == Spec.ECDSA.ecdsa_verification_agile (Spec.ECDSA.Hash SHA2_384) (publicKeyX, publicKeyY) r s (v mLen) (as_seq h0 m)
   )


[@ (Comment "  The input of the function is considered to be public, 
  thus this code is not secret independent with respect to the operations done over the input.
  \n Input: m buffer: uint8 [mLen], \n pub(lic)Key: uint8[64], \n r: uint8[32], \n s: uint8[32]. 
  \n Output: bool, where true stands for the correct signature verification. ")]
val ecdsa_verif_p256_sha512:
    mLen: size_t
  -> m: lbuffer uint8 mLen
  -> pubKey: lbuffer uint8 (size 64)
  -> r: lbuffer uint8 (size 32)
  -> s: lbuffer uint8 (size 32) ->
   Stack bool
    (requires fun h -> live h pubKey /\ live h r /\ live h s /\ live h m)
    (ensures fun h0 result h1 ->
      assert_norm (pow2 32 < pow2 61); 
      let publicKeyX = nat_from_bytes_be (as_seq h1 (gsub pubKey (size 0) (size 32))) in
      let publicKeyY = nat_from_bytes_be (as_seq h1 (gsub pubKey (size 32) (size 32))) in
      let r = nat_from_bytes_be (as_seq h1 r) in
      let s = nat_from_bytes_be (as_seq h1 s) in
      modifies0 h0 h1 /\
      result == Spec.ECDSA.ecdsa_verification_agile (Spec.ECDSA.Hash SHA2_512) (publicKeyX, publicKeyY) r s (v mLen) (as_seq h0 m)
   )

[@ (Comment " The input of the function is considered to be public, 
  thus this code is not secret independent with respect to the operations done over the input.
  \n Input: m buffer: uint8 [mLen], \n pub(lic)Key: uint8[64], \n r: uint8[32], \n s: uint8[32]. 
  \n Output: bool, where true stands for the correct signature verification.
  \n The message m is expected to be hashed by a strong hash function, the lenght of the message is expected to be 32 bytes and more.")]
val ecdsa_verif_without_hash:
  mLen: size_t {uint_v mLen >= Spec.ECDSA.min_input_length Spec.ECDSA.NoHash}
  -> m:lbuffer uint8 mLen
  -> pubKey:lbuffer uint8 (size 64)
  -> r:lbuffer uint8 (size 32)
  -> s:lbuffer uint8 (size 32)
  -> 
  Stack bool
    (requires fun h -> live h pubKey /\ live h r /\ live h s /\ live h m)
    (ensures fun h0 result h1 ->
      let publicKeyX = nat_from_bytes_be (as_seq h1 (gsub pubKey (size 0) (size 32))) in
      let publicKeyY = nat_from_bytes_be (as_seq h1 (gsub pubKey (size 32) (size 32))) in
      let r = nat_from_bytes_be (as_seq h1 r) in
      let s = nat_from_bytes_be (as_seq h1 s) in
      modifies0 h0 h1 /\
      result == Spec.ECDSA.ecdsa_verification_agile Spec.ECDSA.NoHash (publicKeyX, publicKeyY) r s (v mLen)  (as_seq h0 m)
   )


[@@ CPrologue "
/******************/
/* Key validation */
/******************/
";
(Comment "Validate a public key.

  \n  The input of the function is considered to be public, 
  thus this code is not secret independent with respect to the operations done over the input.
  \n Input: pub(lic)Key: uint8[64]. 
  \n Output: bool, where 0 stands for the public key to be correct with respect to SP 800-56A:  \n Verify that the public key is not the “point at infinity”, represented as O. \n Verify that the affine x and y coordinates of the point represented by the public key are in the range [0, p – 1] where p is the prime defining the finite field. \n Verify that y2 = x3 + ax + b where a and b are the coefficients of the curve equation. \n Verify that nQ = O (the point at infinity), where n is the order of the curve and Q is the public key point.
  \n The last extract is taken from : https://neilmadden.blog/2017/05/17/so-how-do-you-validate-nist-ecdh-public-keys/")]
val verify_q: 
  pubKey: lbuffer uint8 (size 64) ->
  Stack bool
    (requires fun h -> live h pubKey)
    (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
      (
        let publicKeyX = nat_from_bytes_be (as_seq h1 (gsub pubKey (size 0) (size 32))) in 
        let publicKeyY = nat_from_bytes_be (as_seq h1 (gsub pubKey (size 32) (size 32))) in
        let pkJ = Spec.P256.toJacobianCoordinates (publicKeyX, publicKeyY) in 
        r == Spec.ECDSA.verifyQValidCurvePointSpec pkJ
      )
    )

[@@ CPrologue "
/*****************************************/
/* Point representations and conversions */
/*****************************************/

/*
  Elliptic curve points have 2 32-byte coordinates (x, y) and can be represented in 3 ways:

  - \"raw\" form (64 bytes): the concatenation of the 2 coordinates, also known as \"internal\"
  - \"compressed\" form (33 bytes): the first byte is either \x02 or \x03, followed by x
  - \"uncompressed\" form (65 bytes): the first byte is always \04, followed by the \"raw\" form

  For all of the conversation functions below, the input and output MUST NOT overlap.
*/
";
 (Comment "Convert 65-byte uncompressed to raw.

This function effectively strips the first byte of the uncompressed representation.

  \n \n Input: a point in not compressed form (uint8[65]), \n result: uint8[64] (internal point representation).
  \n Output: bool, where true stands for the correct decompression.
 ")]
val decompression_not_compressed_form: b: notCompressedForm -> result: lbuffer uint8 (size 64) -> Stack bool 
  (requires fun h -> live h b /\ live h result /\ disjoint b result)
  (ensures fun h0 r h1 -> modifies (loc result) h0 h1 /\
    (
      let id = Lib.Sequence.index (as_seq h0 b) 0 in 
      let x = Lib.Sequence.sub (as_seq h0 b) 1 32 in 
      let xResult = Lib.Sequence.sub (as_seq h1 result) 0 32 in 
      let y = Lib.Sequence.sub (as_seq h0 b) 33 32 in 
      let yResult = Lib.Sequence.sub (as_seq h1 result) 32 32 in 
      if uint_v id = 4 then 
	r == true /\ x == xResult /\ y == yResult
      else 
	r == false
    )
)


[@ (Comment "Convert 33-byte compressed to raw.

Input: a point in compressed form (uint8[33]), \n result: uint8[64] (internal point representation).
  \n Output: bool, where true stands for the correct decompression.
 ")]
val decompression_compressed_form: b: compressedForm -> result: lbuffer uint8 (size 64) -> Stack bool 
  (requires fun h -> live h b /\ live h result /\ disjoint b result)
  (ensures fun h0 r h1 -> 
    (
      let id = Lib.Sequence.index (as_seq h0 b) 0 in 
      let xSequence = Lib.Sequence.sub (as_seq h0 b) 1 32 in 
      let x =  Lib.ByteSequence.nat_from_bytes_be xSequence in 
      if uint_v id = 2 || uint_v id = 3 then
        if x < prime256 then 
          r == true /\ 
        (
          let y = 
            let sq = sq_root_spec (((x * x * x + Spec.P256.aCoordinateP256 * x + Spec.P256.bCoordinateP256) % prime256)) in 
              if (uint_v id) % 2 = (sq % 2) then 
                sq
              else
              (0 - sq) % prime256 
          in 
          as_seq h1 (gsub result (size 0) (size 32)) == xSequence /\
          as_seq h1 (gsub result (size 32) (size 32)) == Lib.ByteSequence.nat_to_bytes_be 32 y)
        else 
          r == false
      else 
        r == false
    ) /\
    modifies (loc result) h0 h1
  )


[@ (Comment "Convert raw to 65-byte uncompressed.

This function effectively prepends a 0x04 byte.

Input: a point buffer (internal representation: uint8[64]), \n result: a point in not compressed form (uint8[65]).")]
val compression_not_compressed_form: b: lbuffer uint8 (size 64) -> result: notCompressedForm -> 
  Stack unit 
    (requires fun h -> live h b /\ live h result /\ disjoint b result)
    (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
      (
        let id = Lib.Sequence.index (as_seq h1 result) 0 in 
        let x = Lib.Sequence.sub (as_seq h0 b) 0 32 in 
        let xResult = Lib.Sequence.sub (as_seq h1 result) 1 32 in 
        let y = Lib.Sequence.sub (as_seq h0 b) 32 32 in 
        let yResult = Lib.Sequence.sub (as_seq h1 result) 33 32 in 
        uint_v id == 4 /\ xResult == x /\ yResult == y  
      )
    )


[@ (Comment "Convert raw to 33-byte compressed.

  Input: `b`, the pointer buffer in internal representation, of type `uint8[64]`
  Output: `result`, a point in compressed form, of type `uint8[33]`
")]
val compression_compressed_form: b: lbuffer uint8 (size 64) -> result: compressedForm -> 
  Stack unit 
    (requires fun h -> live h b /\ live h result /\ disjoint b result)
    (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
      (
        let identifier = Lib.Sequence.index (as_seq h1 result) 0 in 
        let x = Lib.Sequence.sub (as_seq h0 b) 0 32 in 
        let xResult = Lib.Sequence.sub (as_seq h1 result) 1 32 in 
        let y = Lib.Sequence.sub (as_seq h0 b) 32 32 in 
        uint_v identifier == (Lib.ByteSequence.nat_from_intseq_be y % pow2 1)  + 2 /\
        x == xResult  
      )  
  )


[@@ CPrologue "
/******************/
/* ECDH agreement */
/******************/";

(Comment "Convert a private key into a raw public key.

  Input: `scalar`, the private key, of type `uint8[32]`.
  Output: `result`, the public key, of type `uint8[64]`.
  Returns:
  - `true`, for success, meaning the public key is not a point at infinity
  - `false`, otherwise.

  `scalar` and `result` MUST NOT overlap.")]
val ecp256dh_i:
    result:lbuffer uint8 (size 64)
  -> scalar:lbuffer uint8 (size 32)
  -> Stack bool
  (requires fun h ->
    live h result /\ live h scalar /\ 
    disjoint result scalar)
  (ensures fun h0 r h1 ->
    let pointX, pointY, flag = ecp256_dh_i (as_seq h0 scalar) in
    modifies (loc result) h0 h1 /\
    r == flag /\
    as_seq h1 (gsub result (size 0) (size 32)) == pointX /\
    as_seq h1 (gsub result (size 32) (size 32)) == pointY)


[@ (Comment "ECDH key agreement.

This function takes a 32-byte secret key, another party's 64-byte raw public
key, and computeds the 64-byte ECDH shared key.

The user MUST validate keys with `is_more_than_zero_less_than_order` and
`verify_q`.

   The pub(lic)_key input of the function is considered to be public, 
  thus this code is not secret independent with respect to the operations done over this variable.
  \n Input: result: uint8[64], \n pub(lic)Key: uint8[64], \n scalar: uint8[32].
  \n Output: bool, where True stands for the correct key generation. False value means that an error has occurred (possibly the provided public key was incorrect or the result represents point at infinity). 
  ")]
val ecp256dh_r:
    result:lbuffer uint8 (size 64)
  -> pubKey:lbuffer uint8 (size 64)
  -> scalar:lbuffer uint8 (size 32)
  -> Stack bool
    (requires fun h ->
      live h result /\ live h pubKey /\ live h scalar /\
      disjoint result pubKey /\ disjoint result scalar)
    (ensures fun h0 r h1 ->
      let pubKeyX = gsub pubKey (size 0) (size 32) in
      let pubKeyY = gsub pubKey (size 32) (size 32) in
      let pointX, pointY, flag =
        ecp256_dh_r (as_seq h0 pubKeyX) (as_seq h0 pubKeyY) (as_seq h0 scalar) in
      r == flag /\
      modifies (loc result) h0 h1 /\
      as_seq h1 (gsub result (size 0) (size 32)) == pointX /\
      as_seq h1 (gsub result (size 32) (size 32)) == pointY)

[@@ CPrologue "
/******************/
/* Key validation */
/******************/
";
(Comment "Validate a private key.

Input: scalar: uint8[32].
  \n Output: bool, where true stands for the scalar to be more than 0 and less than order.")]
val is_more_than_zero_less_than_order: x: lbuffer uint8 (size 32) -> Stack bool
  (requires fun h -> live h x)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    (
      let scalar = nat_from_bytes_be (as_seq h0 x) in 
      r <==> (scalar > 0 && scalar < prime_p256_order)
    )
  )
