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

open Hacl.Spec.P256
open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.Definitions

open Hacl.Spec.ECDSAP256.Definition

open Hacl.Impl.LowLevel

open Hacl.Impl.P256

open Hacl.Impl.ECDSA.MM.Exponent
open Hacl.Impl.ECDSA.MontgomeryMultiplication

open Hacl.Impl.ECDSA.P256SHA256.Common

open Hacl.Impl.ECDSA.P256SHA256.KeyGeneration
open Hacl.Impl.ECDSA.P256SHA256.Signature
open Hacl.Impl.ECDSA.P256SHA256.Verification


val ecdsa_p256_sha2_keyGen: result: lbuffer uint8 (size 64) -> privKey: lbuffer uint8 (size 32) -> 
  Stack unit 
    (requires fun h -> 
      live h result /\ live h privKey /\
      disjoint result privKey /\
      nat_from_bytes_le (as_seq h privKey) < prime_p256_order
    )
    (ensures fun h0 _ h1 -> 
      modifies (loc result) h0 h1 /\
      (
	let publicKeyX = nat_from_bytes_le (as_seq h1 (gsub result (size 0) (size 32))) in 
	let publicKeyY = nat_from_bytes_le (as_seq h1 (gsub result (size 32) (size 32))) in 
	let xN, yN, _ = secret_to_public (as_seq h0 privKey) in 
	publicKeyX < prime256 /\ 
	publicKeyY < prime256 /\
	publicKeyX == xN /\
	publicKeyY == yN
      )
    )

let ecdsa_p256_sha2_keyGen result privKey = key_gen result privKey


val ecdsa_p256_sha2_sign: result: lbuffer uint8 (size 64) -> mLen: size_t -> m: lbuffer uint8 mLen {uint_v mLen < Spec.Hash.Definitions.max_input_length (Spec.Hash.Definitions.SHA2_256)} ->
  privKey: lbuffer uint8 (size 32) -> 
  k: lbuffer uint8 (size 32) -> 
  Stack uint64
  (requires fun h -> 
    live h result /\ live h m /\ live h privKey /\ live h k /\
    LowStar.Monotonic.Buffer.all_disjoint [loc result; loc m; loc privKey; loc k] /\
    nat_from_bytes_le (as_seq h m) < prime_p256_order /\
    nat_from_bytes_le (as_seq h privKey) < prime_p256_order /\
    nat_from_bytes_le (as_seq h k) < prime_p256_order
  )
  (ensures fun h0 flag h1 -> 
    modifies (loc result) h0 h1 /\
     (
      let resultR = gsub result (size 0) (size 32) in 
      let resultS = gsub result (size 32) (size 32) in 
      let r, s, flagSpec = Hacl.Spec.ECDSA.ecdsa_signature (uint_v mLen) (as_seq h0 m) (as_seq h0 privKey) (as_seq h0 k) in 
      let resultR = nat_from_bytes_le (as_seq h1 resultR) in 
      let resultS = nat_from_bytes_le (as_seq h1 resultS) in 
      flag == flagSpec /\ r == resultR /\ s == resultS
    )    
  )

let ecdsa_p256_sha2_sign result mLen m privKey k = ecdsa_signature result mLen m privKey k


val ecdsa_p256_sha2_sign_nist: result: lbuffer uint8 (size 64) -> m: lbuffer uint8 (size 32) -> 
  privKey: lbuffer uint8 (size 32) -> 
  k: lbuffer uint8 (size 32) -> 
  Stack uint64
  (requires fun h -> 
    live h result /\ live h m /\ live h privKey /\ live h k /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc result; loc m; loc privKey; loc k] /\
    nat_from_bytes_le (as_seq h m) < prime_p256_order /\
    nat_from_bytes_le (as_seq h privKey) < prime_p256_order /\
    nat_from_bytes_le (as_seq h k) < prime_p256_order
  )
  (ensures fun h0 flag h1 -> 
    modifies (loc result) h0 h1 /\ 
    (
      let resultR = gsub result (size 0) (size 32) in 
      let resultS = gsub result (size 32) (size 32) in 
      let r, s, flagSpec = Hacl.Spec.ECDSA.ecdsa_signature_nist_compliant (as_seq h0 m) (as_seq h0 privKey) (as_seq h0 k) in 
      let resultR = nat_from_bytes_le (as_seq h1 resultR) in 
      let resultS = nat_from_bytes_le (as_seq h1 resultS) in 
      flag == flagSpec /\ r == resultR /\ s == resultS
    )
  )

let ecdsa_p256_sha2_sign_nist result m privKey k = ecdsa_signature_nist_compliant result m privKey k


val ecdsa_p256_sha2_verify: mLen: size_t ->  m: lbuffer uint8 mLen {uint_v mLen < Spec.Hash.Definitions.max_input_length (Spec.Hash.Definitions.SHA2_256)} ->
  pubKey: lbuffer uint64 (size 8) -> 
  r: lbuffer uint64 (size 4) -> 
  s: lbuffer uint64 (size 4) ->
  Stack bool
    (requires fun h -> 
      live h pubKey /\ live h r /\ live h s /\ live h m /\
      LowStar.Monotonic.Buffer.all_disjoint [loc pubKey; loc r; loc s; loc m]
    )  
    (ensures fun h0 result h1 -> 
      modifies0 h0 h1 /\
      (
	let pubKeyX = as_nat h0 (gsub pubKey (size 0) (size 4)) in 
	let pubKeyY = as_nat h0 (gsub pubKey (size 4) (size 4)) in 
	result == Hacl.Spec.ECDSA.ecdsa_verification (pubKeyX, pubKeyY) (as_nat h0 r) (as_nat h0 s) (v mLen) (as_seq h0 m)
      )
    )

let ecdsa_p256_sha2_verify mLen m pubKey r s = ecdsa_verification pubKey r s mLen m

val ecdsa_p256_sha2_verify_u8: pubKey: lbuffer uint8 (size 64) -> r: lbuffer uint8 (size 32) -> s: lbuffer uint8 (size 32) -> 
  mLen: size_t ->
  m: lbuffer uint8 mLen {uint_v mLen < Spec.Hash.Definitions.max_input_length (Spec.Hash.Definitions.SHA2_256)} ->
  Stack bool
      (requires fun h -> 
	live h pubKey /\ live h r /\ live h s /\ live h m /\
	LowStar.Monotonic.Buffer.all_disjoint [loc pubKey; loc r; loc s; loc m]
      )  
    (ensures fun h0 result h1 -> modifies0 h0 h1 /\ 
      (
	let publicKeyX =  nat_from_bytes_le (as_seq h1 (gsub pubKey (size 0) (size 32))) in 
	let publicKeyY =  nat_from_bytes_le (as_seq h1 (gsub pubKey (size 32) (size 32))) in 
	let r = nat_from_bytes_le (as_seq h1 r) in 
	let s = nat_from_bytes_le (as_seq h1 s) in 
	result == Hacl.Spec.ECDSA.ecdsa_verification (publicKeyX, publicKeyY) r s (v mLen) (as_seq h0 m)
    )
  )

let ecdsa_p256_sha2_verify_u8 pubKey r s mLen m = ecdsa_verification_u8 pubKey r s mLen m
