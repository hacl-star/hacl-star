module Hacl.P256

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence

open FStar.Mul
open Spec.ECC
open Spec.ECC.Curves
(* open Spec.ECC.Lemmas *)
open Hacl.Spec.EC.Definition
open Spec.Hash.Definitions

open Spec.DH
open Hacl.Impl.P256.Compression
open Hacl.Spec.MontgomeryMultiplication


[@ (Comment " Input: result buffer: uint8[64], \n m buffer: uint8 [mLen], \n priv(ate)Key: uint8[32], \n k (nonce): uint32[32]. 
  \n Output: uint64, where 0 stands for the correct signature generation. All the other values mean that an error has occurred. 
  \n The private key and the nonce are expected to be less than the curve order.")]
val ecdsa_sign_p256_sha2: result: lbuffer uint8 (size 64) 
  -> mLen: size_t 
  -> m: lbuffer uint8 mLen 
  -> privKey: lbuffer uint8 (size 32) 
  -> k: lbuffer uint8 (size 32) -> 
  Stack uint64
  (requires fun h -> 
    live h result /\ live h m /\ live h privKey /\ live h k /\
    disjoint result m /\
    disjoint result privKey /\
    disjoint result k /\
    nat_from_bytes_be (as_seq h privKey) < (getOrder #P256) /\
    nat_from_bytes_be (as_seq h k) < (getOrder #P256)
  )
  (ensures fun h0 flag h1 -> 
    modifies (loc result) h0 h1 /\
     (assert_norm (pow2 32 < pow2 61);
      let resultR = gsub result (size 0) (size 32) in 
      let resultS = gsub result (size 32) (size 32) in 
      let r, s, flagSpec = Spec.ECDSA.ecdsa_signature P256 (Spec.ECDSA.Hash SHA2_256) (uint_v mLen) (as_seq h0 m) (as_seq h0 privKey) (as_seq h0 k) in 
      as_seq h1 resultR == nat_to_bytes_be 32 r /\
      as_seq h1 resultS == nat_to_bytes_be 32 s /\
      flag == flagSpec 
    ))    
  

[@ (Comment " Input: result buffer: uint8[64], \n m buffer: uint8 [mLen], \n priv(ate)Key: uint8[32], \n k (nonce): uint32[32]. 
  \n Output: uint64, where 0 stands for the correct signature generation. All the other values mean that an error has occurred. 
  \n The private key and the nonce are expected to be less than the curve order.")]
val ecdsa_sign_p256_sha384: result: lbuffer uint8 (size 64) -> mLen: size_t -> m: lbuffer uint8 mLen ->
  privKey: lbuffer uint8 (size 32) -> 
  k: lbuffer uint8 (size 32) -> 
  Stack uint64
  (requires fun h -> 
    live h result /\ live h m /\ live h privKey /\ live h k /\
    disjoint result m /\
    disjoint result privKey /\
    disjoint result k /\
    nat_from_bytes_be (as_seq h privKey) < (getOrder #P256) /\
    nat_from_bytes_be (as_seq h k) < (getOrder #P256)
  )
  (ensures fun h0 flag h1 -> 
    modifies (loc result) h0 h1 /\
     (assert_norm (pow2 32 < pow2 61);
      let resultR = gsub result (size 0) (size 32) in 
      let resultS = gsub result (size 32) (size 32) in 
      let r, s, flagSpec = Spec.ECDSA.ecdsa_signature P256 (Spec.ECDSA.Hash SHA2_384) (uint_v mLen) (as_seq h0 m) (as_seq h0 privKey) (as_seq h0 k) in 
      as_seq h1 resultR == nat_to_bytes_be 32 r /\
      as_seq h1 resultS == nat_to_bytes_be 32 s /\
      flag == flagSpec 
    )    
  )


[@ (Comment " Input: result buffer: uint8[64], \n m buffer: uint8 [mLen], \n priv(ate)Key: uint8[32], \n k (nonce): uint32[32]. 
  \n Output: uint64, where 0 stands for the correct signature generation. All the other values mean that an error has occurred. 
  \n The private key and the nonce are expected to be less than the curve order.")]
val ecdsa_sign_p256_sha512: result: lbuffer uint8 (size 64) 
  -> mLen: size_t 
  -> m: lbuffer uint8 mLen 
  -> privKey: lbuffer uint8 (size 32) 
  -> k: lbuffer uint8 (size 32) -> 
  Stack uint64
  (requires fun h -> 
    live h result /\ live h m /\ live h privKey /\ live h k /\
    disjoint result m /\
    disjoint result privKey /\
    disjoint result k /\
    nat_from_bytes_be (as_seq h privKey) < (getOrder #P256) /\
    nat_from_bytes_be (as_seq h k) < (getOrder #P256)
  )
  (ensures fun h0 flag h1 -> 
    modifies (loc result) h0 h1 /\
     (assert_norm (pow2 32 < pow2 61);
      let resultR = gsub result (size 0) (size 32) in 
      let resultS = gsub result (size 32) (size 32) in 
      let r, s, flagSpec = Spec.ECDSA.ecdsa_signature P256 (Spec.ECDSA.Hash SHA2_512) (uint_v mLen) (as_seq h0 m) (as_seq h0 privKey) (as_seq h0 k) in 
      as_seq h1 resultR == nat_to_bytes_be 32 r /\
      as_seq h1 resultS == nat_to_bytes_be 32 s /\
      flag == flagSpec 
    )    
  )

[@ (Comment " Input: result buffer: uint8[64], \n m buffer: uint8 [mLen], \n priv(ate)Key: uint8[32], \n k (nonce): uint32[32]. 
  \n Output: uint64, where 0 stands for the correct signature generation. All the other values mean that an error has occurred. 
  \n The private key and the nonce are expected to be less than the curve order. 
  \n The message m is expected to be hashed by a strong hash function, the lenght of the message is expected to be 32 bytes and more.")]
val ecdsa_sign_p256_without_hash: result: lbuffer uint8 (size 64) 
  -> mLen: size_t {uint_v mLen >= Spec.ECDSA.min_input_length #P256 Spec.ECDSA.NoHash}
  -> m: lbuffer uint8 mLen
  -> privKey: lbuffer uint8 (size 32) 
  -> k: lbuffer uint8 (size 32) -> 
  Stack uint64
  (requires fun h -> 
    live h result /\ live h m /\ live h privKey /\ live h k /\
    disjoint result m /\
    disjoint result privKey /\
    disjoint result k /\
    nat_from_bytes_be (as_seq h privKey) < (getOrder #P256) /\
    nat_from_bytes_be (as_seq h k) < (getOrder #P256)
  )
  (ensures fun h0 flag h1 -> 
    modifies (loc result) h0 h1 /\
     (assert_norm (pow2 32 < pow2 61);
      let resultR = gsub result (size 0) (size 32) in 
      let resultS = gsub result (size 32) (size 32) in 
      let r, s, flagSpec = Spec.ECDSA.ecdsa_signature P256 Spec.ECDSA.NoHash (uint_v mLen) (as_seq h0 m) (as_seq h0 privKey) (as_seq h0 k) in  
      as_seq h1 resultR == nat_to_bytes_be 32 r /\
      as_seq h1 resultS == nat_to_bytes_be 32 s /\
      flag == flagSpec 
    )    
  )

[@ (Comment " This code is not side-channel resistant.
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
      result == Spec.ECDSA.ecdsa_verification P256 (Spec.ECDSA.Hash SHA2_256) (publicKeyX, publicKeyY) r s (v mLen) (as_seq h0 m)
    )

[@ (Comment " This code is not side-channel resistant.
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
      result == Spec.ECDSA.ecdsa_verification P256 (Spec.ECDSA.Hash SHA2_384) (publicKeyX, publicKeyY) r s (v mLen) (as_seq h0 m)
   )


[@ (Comment " This code is not side-channel resistant.
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
      result == Spec.ECDSA.ecdsa_verification P256 (Spec.ECDSA.Hash SHA2_512) (publicKeyX, publicKeyY) r s (v mLen) (as_seq h0 m)
   )


[@ (Comment "This code is not side-channel resistant.
  \n Input: m buffer: uint8 [mLen], \n pub(lic)Key: uint8[64], \n r: uint8[32], \n s: uint8[32]. 
  \n Output: bool, where true stands for the correct signature verification.
  \n The message m is expected to be hashed by a strong hash function, the lenght of the message is expected to be 32 bytes and more.")]
val ecdsa_verif_without_hash:
  mLen: size_t {uint_v mLen >= Spec.ECDSA.min_input_length #P256 Spec.ECDSA.NoHash}
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
      result == Spec.ECDSA.ecdsa_verification P256 Spec.ECDSA.NoHash (publicKeyX, publicKeyY) r s (v mLen)  (as_seq h0 m)
   )


[@ (Comment " Public key verification function. 
  \n This code is not side-channel resistant.
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
        let pkJ = Spec.ECC.toJacobianCoordinates (publicKeyX, publicKeyY) in 
        r == Spec.ECDSA.verifyQValidCurvePointSpec #P256 pkJ
      )
    )

(*)
(*
[@ (Comment " There and further we introduce notions of compressed point and not compressed point. 
  \n We denote || as byte concatenation. 
  \n A compressed point is a point representaion as follows: (0x2 + y % 2) || x.
  \n A not Compressed point is a point representation as follows: 0x4 || x || y.

  \n \n Input: a point in not compressed form (uint8[65]), \n result: uint8[64] (internal point representation).
  \n Output: bool, where true stands for the correct decompression.
 ")]
*)


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

(*
[@ (Comment " Input: a point in compressed form (uint8[33]), \n result: uint8[64] (internal point representation).
  \n Output: bool, where true stands for the correct decompression.
 ")]
*)

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
            let sq = sq_root_spec #P256 (((x * x * x + aCoordinate #P256 * x + bCoordinate #P256) % prime256)) in 
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

(*
[@ (Comment " Input: a point buffer (internal representation: uint8[64]), \n result: a point in not compressed form (uint8[65]).")]
*)


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

(*
[@ (Comment " Input: a point buffer (internal representation: uint8[64]), \n result: a point in not compressed form (uint8[33]).")]
*)

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


(*
[@ (Comment " Input: result: uint8[64], \n scalar: uint8[32].
  \n Output: uint64, where 0 stands for the correct key generation. All the other values mean that an error has occurred. 
  ")]
*)
 *)

val ecp256dh_i:
    result:lbuffer uint8 (size 64)
  -> scalar:lbuffer uint8 (size 32)
  -> Stack uint64
  (requires fun h ->
    live h result /\ live h scalar /\ 
    disjoint result scalar)
  (ensures fun h0 r h1 ->
    let pointX, pointY, flag = ecp256_dh_i #P256 (as_seq h0 scalar) in
    modifies (loc result) h0 h1 /\
    r == flag /\
    as_seq h1 (gsub result (size 0) (size 32)) == pointX /\
    as_seq h1 (gsub result (size 32) (size 32)) == pointY)

(* 
val ecp384dh_i:
    result:lbuffer uint8 (size 96)
  -> scalar:lbuffer uint8 (size 48)
  -> Stack uint64
  (requires fun h ->
    live h result /\ live h scalar /\ 
    disjoint result scalar)
  (ensures fun h0 r h1 ->
    let pointX, pointY, flag = ecp256_dh_i #P384 (as_seq h0 scalar) in
    modifies (loc result) h0 h1 /\
    r == flag /\
    as_seq h1 (gsub result (size 0) (size 48)) == pointX /\
    as_seq h1 (gsub result (size 48) (size 48)) == pointY)
 *)



[@ (Comment " This code is not side channel resistant on pub_key. \n Input: result: uint8[64], \n pub(lic)Key: uint8[64], \n scalar: uint8[32].
  \n Output: uint64, where 0 stands for the correct key generation. All the other values mean that an error has occurred. 
  ")] 
val ecp256dh_r:
    result:lbuffer uint8 (size 64)
  -> pubKey:lbuffer uint8 (size 64)
  -> scalar:lbuffer uint8 (size 32)
  -> Stack uint64
    (requires fun h ->
      live h result /\ live h pubKey /\ live h scalar /\
      disjoint result pubKey /\ disjoint result scalar)
    (ensures fun h0 r h1 ->
      let pubKeyX = gsub pubKey (size 0) (size 32) in
      let pubKeyY = gsub pubKey (size 32) (size 32) in
      let pointX, pointY, flag =
        ecp256_dh_r #P256 (as_seq h0 pubKeyX) (as_seq h0 pubKeyY) (as_seq h0 scalar) in
      r == flag /\
      modifies (loc result) h0 h1 /\
      as_seq h1 (gsub result (size 0) (size 32)) == pointX /\
      as_seq h1 (gsub result (size 32) (size 32)) == pointY)





(*
[@ (Comment " This code is not side channel resistant on pub_key. \n Input: result: uint8[64], \n pub(lic)Key: uint8[64], \n scalar: uint8[32].
  \n Output: uint64, where 0 stands for the correct key generation. All the other values mean that an error has occurred. 
  ")]



val ecp384dh_r:
    result:lbuffer uint8 (size 96)
  -> pubKey:lbuffer uint8 (size 96)
  -> scalar:lbuffer uint8 (size 48)
  -> Stack uint64
    (requires fun h ->
      live h result /\ live h pubKey /\ live h scalar /\
      disjoint result pubKey /\ disjoint result scalar)
    (ensures fun h0 r h1 ->
      let pubKeyX = gsub pubKey (size 0) (size 48) in
      let pubKeyY = gsub pubKey (size 48) (size 48) in
      let pointX, pointY, flag =
        ecp256_dh_r #P384 (as_seq h0 pubKeyX) (as_seq h0 pubKeyY) (as_seq h0 scalar) in
      r == flag /\
      modifies (loc result) h0 h1 /\
      as_seq h1 (gsub result (size 0) (size 48)) == pointX /\
      as_seq h1 (gsub result (size 48) (size 48)) == pointY)

(* 

 *)


val uploadp256: unit -> Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> modifies0 h0 h1)

val uploadpsmth: unit -> Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> modifies0 h0 h1)
 *)
