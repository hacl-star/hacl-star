module Hacl.P256

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence

open Spec.DH
open Hacl.Spec.ECDSA.Definition

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence

open FStar.Mul

open Spec.ECC
(* open Spec.ECC.Lemmas *)
open Hacl.Spec.EC.Definition

open Spec.ECDSA
open Hacl.Impl.P256.Compression
open Spec.Hash.Definitions

open Hacl.Impl.ECDSA.Signature
open Hacl.Impl.ECDSA.Verification

(*)
let ecdsa_sign_p256_sha2 result mLen m privKey k = 
  ecdsa_signature P256 (Hash SHA2_256) result mLen m privKey k


  let ecdsa_sign_p256_sha384 result mLen m privKey k = 
  ecdsa_signature P256 (Hash SHA2_384) result mLen m privKey k

let ecdsa_sign_p256_sha512 result mLen m privKey k = 
  ecdsa_signature P256 (Hash SHA2_512) result mLen m privKey k

let ecdsa_sign_p256_without_hash result mLen m privKey k = 
  ecdsa_signature P256 NoHash result mLen m privKey k


let ecdsa_verif_p256_sha2 mLen m pubKey r s = 
  ecdsa_verification P256 (Hash SHA2_256) pubKey r s mLen m


let ecdsa_verif_p256_sha384 mLen m pubKey r s = 
  ecdsa_verification P256 (Hash SHA2_384) pubKey r s mLen m

let ecdsa_verif_p256_sha512 mLen m pubKey r s = 
  ecdsa_verification P256 (Hash SHA2_512) pubKey r s mLen m

let ecdsa_verif_without_hash mLen m pubKey r s  =
   ecdsa_verification P256 NoHash pubKey r s mLen m


let verify_q pubKey = 
    Hacl.Impl.P256.Signature.Common.verifyQ #P256 pubKey


let decompression_not_compressed_form b result = 
  Hacl.Impl.P256.Compression.decompressionNotCompressedForm #P256 b result

let decompression_compressed_form b result = 
  Hacl.Impl.P256.Compression.decompressionCompressedForm #P256 b result



let compression_not_compressed_form b result = 
  Hacl.Impl.P256.Compression.compressionNotCompressedForm #P256 b result

let compression_compressed_form b result = 
  Hacl.Impl.P256.Compression.compressionCompressedForm #P256 b result


 *)
let ecp256dh_i result scalar = Hacl.Impl.EC.DH.ecp256dh_i P256 result scalar

let ecp384dh_i result scalar = Hacl.Impl.EC.DH.ecp256dh_i P384 result scalar


let ecp256dh_r result pubKey scalar = Hacl.Impl.EC.DH.ecp256dh_r #P256 result pubKey scalar

let ecp384dh_r result pubKey scalar = Hacl.Impl.EC.DH.ecp256dh_r #P384 result pubKey scalar


inline_for_extraction
class curve_test = {
  len: (a: size_t {v a > 0})
}

val uploadZero: c: curve_test -> l: lbuffer uint64 (c.len) -> Stack unit 
  (requires fun h -> live h l)
  (ensures fun h0 _ h1 -> modifies (loc l) h0 h1)


let uploadZero c l = 
  upd l (size 0) (u64 5)



instance p256: curve_test = {
  len = 10ul}


let uploadp256 () = 
  push_frame();
    let a = p256.len in 
    let b = create a (u64 0) in 
    uploadZero p256 b;
  pop_frame()


instance smth: curve_test = {
  len = 11ul}


let uploadpsmth () = 
  push_frame();
    let a = smth.len in 
    let b = create a (u64 0) in 
    uploadZero smth b;
  pop_frame()
