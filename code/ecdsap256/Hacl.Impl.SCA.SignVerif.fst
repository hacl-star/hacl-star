module Hacl.Impl.SCA.SignVerif

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open FStar.Mul

open Hacl.Impl.ECDSA.P256.Signature.Agile
open Hacl.Impl.ECDSA.P256.Verification.Agile
open Hacl.Impl.P256.DH

open Spec.ECDSA

assume val boolToU64: a: bool -> Tot uint64


val ecdsa_signature_h: alg: hash_alg_ecdsa
  -> result: lbuffer uint8 (size 64) 
  -> mLen: size_t {v mLen >= Spec.ECDSA.min_input_length alg} 
  -> m: lbuffer uint8 mLen 
  -> privKey: lbuffer uint8 (size 32)
  -> k: lbuffer uint8 (size 32)  ->
  Stack uint64
    (requires fun h -> 
      live h result /\ live h m /\ live h privKey /\ live h k /\
      disjoint result m /\
      disjoint result privKey /\
      disjoint result k)
    (ensures fun h0 _ h1 -> True)


let ecdsa_signature_h alg result mLen m privKey k = 
  push_frame();
    let publicKey = create (size 64) (u8 0) in 
  let flagSignature = ecdsa_signature_defensive alg result mLen m privKey k in 
    let r = sub result (size 0) (size 32) in 
    let s = sub result (size 32) (size 32) in 
  let publicKeyGenFlag = ecp256dh_i publicKey privKey in 
  let flagVerification = ecdsa_verification alg publicKey r s mLen m in 
  let flagVerificatinAsUint64 = boolToU64 flagVerification in 
    pop_frame();
  eq_mask (eq_mask flagSignature publicKeyGenFlag) flagVerificatinAsUint64
  
