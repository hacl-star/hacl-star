module Hacl.Impl.ECDSA

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence

open FStar.Mul
open FStar.Math.Lemmas

open Hacl.Hash.SHA2

open Spec.P256
open Spec.P256.Lemmas
open Spec.P256.Definitions
open Spec.Hash.Definitions

open Spec.ECDSAP256.Definition

open Hacl.Impl.LowLevel

open Hacl.Impl.P256

open Hacl.Impl.ECDSA.MM.Exponent
open Hacl.Impl.ECDSA.MontgomeryMultiplication

open Hacl.Impl.P256.Signature.Common

open Hacl.Impl.P256.Compression

open Hacl.Impl.ECDSA.P256SHA256.Signature.Agile
open Hacl.Impl.ECDSA.P256SHA256.Signature.Blake2

open Hacl.Impl.ECDSA.P256SHA256.Verification.Agile

open Spec.P256.MontgomeryMultiplication


val secretToPublicU8: result: lbuffer uint8 (size 64) -> scalar: lbuffer uint8 (size 32) -> tempBuffer: lbuffer uint64 (size 100) ->
  Stack unit
    (requires fun h -> 
      live h result /\ live h scalar /\ live h tempBuffer /\ 
      LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer; loc scalar; loc result]
    )
  (
    ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer) h0 h1 
  )


val ecdsa_p256_sha2_sign: result: lbuffer uint8 (size 64) -> mLen: size_t -> m: lbuffer uint8 mLen ->
  privKey: lbuffer uint8 (size 32) -> 
  k: lbuffer uint8 (size 32) -> 
  Stack uint64
  (requires fun h -> 
    live h result /\ live h m /\ live h privKey /\ live h k /\
    disjoint result m /\
    disjoint result privKey /\
    disjoint result k /\
    nat_from_bytes_be (as_seq h privKey) < prime_p256_order /\
    nat_from_bytes_be (as_seq h k) < prime_p256_order
  )
  (ensures fun h0 flag h1 -> 
    modifies (loc result) h0 h1 /\
     (assert_norm (pow2 32 < pow2 61);
      let resultR = gsub result (size 0) (size 32) in 
      let resultS = gsub result (size 32) (size 32) in 
      let r, s, flagSpec = Spec.ECDSA.ecdsa_signature_agile SHA2_256 (uint_v mLen) (as_seq h0 m) (as_seq h0 privKey) (as_seq h0 k) in 
      as_seq h1 resultR == nat_to_bytes_be 32 r /\
      as_seq h1 resultS == nat_to_bytes_be 32 s /\
      flag == flagSpec 
    )    
  )


val ecdsa_p256_sha2_384_sign: result: lbuffer uint8 (size 64) -> mLen: size_t -> m: lbuffer uint8 mLen ->
  privKey: lbuffer uint8 (size 32) -> 
  k: lbuffer uint8 (size 32) -> 
  Stack uint64
  (requires fun h -> 
    live h result /\ live h m /\ live h privKey /\ live h k /\
    disjoint result m /\
    disjoint result privKey /\
    disjoint result k /\
    nat_from_bytes_be (as_seq h privKey) < prime_p256_order /\
    nat_from_bytes_be (as_seq h k) < prime_p256_order
  )
  (ensures fun h0 flag h1 -> 
    modifies (loc result) h0 h1 /\
     (assert_norm (pow2 32 < pow2 61);
      let resultR = gsub result (size 0) (size 32) in 
      let resultS = gsub result (size 32) (size 32) in 
      let r, s, flagSpec = Spec.ECDSA.ecdsa_signature_agile SHA2_384 (uint_v mLen) (as_seq h0 m) (as_seq h0 privKey) (as_seq h0 k) in 
      as_seq h1 resultR == nat_to_bytes_be 32 r /\
      as_seq h1 resultS == nat_to_bytes_be 32 s /\
      flag == flagSpec 
    )    
  )


val ecdsa_p256_sha2_512_sign: result: lbuffer uint8 (size 64) -> mLen: size_t -> m: lbuffer uint8 mLen ->
  privKey: lbuffer uint8 (size 32) -> 
  k: lbuffer uint8 (size 32) -> 
  Stack uint64
  (requires fun h -> 
    live h result /\ live h m /\ live h privKey /\ live h k /\
    disjoint result m /\
    disjoint result privKey /\
    disjoint result k /\
    nat_from_bytes_be (as_seq h privKey) < prime_p256_order /\
    nat_from_bytes_be (as_seq h k) < prime_p256_order
  )
  (ensures fun h0 flag h1 -> 
    modifies (loc result) h0 h1 /\
     (assert_norm (pow2 32 < pow2 61);
      let resultR = gsub result (size 0) (size 32) in 
      let resultS = gsub result (size 32) (size 32) in 
      let r, s, flagSpec = Spec.ECDSA.ecdsa_signature_agile SHA2_512 (uint_v mLen) (as_seq h0 m) (as_seq h0 privKey) (as_seq h0 k) in 
      as_seq h1 resultR == nat_to_bytes_be 32 r /\
      as_seq h1 resultS == nat_to_bytes_be 32 s /\
      flag == flagSpec 
    )    
  )


val ecdsa_signature_blake2: result: lbuffer uint8 (size 64) -> mLen: size_t -> m: lbuffer uint8 mLen ->
  privKey: lbuffer uint8 (size 32) -> 
  k: lbuffer uint8 (size 32) -> 
  Stack uint64
  (requires fun h -> 
    live h result /\ live h m /\ live h privKey /\ live h k /\
    disjoint result m /\
    disjoint result privKey /\
    disjoint result k /\
    nat_from_bytes_be (as_seq h privKey) < prime_p256_order /\
    nat_from_bytes_be (as_seq h k) < prime_p256_order
  )
  (ensures fun h0 flag h1 -> 
    modifies (loc result) h0 h1 /\
     (assert_norm (pow2 32 < pow2 61);
      let resultR = gsub result (size 0) (size 32) in 
      let resultS = gsub result (size 32) (size 32) in 
      let r, s, flagSpec = Spec.ECDSA.ecdsa_signature_blake2 (uint_v mLen) (as_seq h0 m) (as_seq h0 privKey) (as_seq h0 k) in 
      as_seq h1 resultR == nat_to_bytes_be 32 r /\
      as_seq h1 resultS == nat_to_bytes_be 32 s /\
      flag == flagSpec 
    )    
  )



(* This code is not side channel resistant *)
val ecdsa_p256_sha2_verification:
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
      result == Spec.ECDSA.ecdsa_verification_agile SHA2_256 (publicKeyX, publicKeyY) r s (v mLen) (as_seq h0 m))


val ecdsa_verification_blake2:
    mLen:size_t
  -> m:lbuffer uint8 mLen
  -> pubKey:lbuffer uint8 (size 64)
  -> r:lbuffer uint8 (size 32)
  -> s:lbuffer uint8 (size 32) ->
  Stack bool
    (requires fun h -> live h pubKey /\ live h r /\ live h s /\ live h m)
    (ensures fun h0 result h1 ->
      let publicKeyX = nat_from_bytes_be (as_seq h1 (gsub pubKey (size 0) (size 32))) in
      let publicKeyY = nat_from_bytes_be (as_seq h1 (gsub pubKey (size 32) (size 32))) in
      let r = nat_from_bytes_be (as_seq h1 r) in
      let s = nat_from_bytes_be (as_seq h1 s) in
      modifies0 h0 h1 /\
      result == Spec.ECDSA.ecdsa_verification_blake2 (publicKeyX, publicKeyY) r s (v mLen) (as_seq h0 m))




val decompressionNotCompressedForm: b: notCompressedForm -> result: lbuffer uint8 (size 64) -> Stack bool 
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


val decompressionCompressedForm: b: compressedForm -> result: lbuffer uint8 (size 64) -> Stack bool 
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
  r == false) /\
  modifies (loc result) h0 h1)


val compressionNotCompressedForm: b: lbuffer uint8 (size 64) -> result: notCompressedForm -> 
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


val compressionCompressedForm: b: lbuffer uint8 (size 64) -> result: compressedForm -> 
  Stack unit 
    (requires fun h -> live h b /\ live h result /\ disjoint b result)
    (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
      (
        let identifier = Lib.Sequence.index (as_seq h1 result) 0 in 
        let x = Lib.Sequence.sub (as_seq h0 b) 0 32 in 
    let xResult = Lib.Sequence.sub (as_seq h1 result) 1 32 in 
        let y = Lib.Sequence.sub (as_seq h0 b) 32 32 in 
        uint_v identifier == (Lib.ByteSequence.nat_from_intseq_le y % pow2 1)  + 2 /\
  x == xResult  
      )  
  )

