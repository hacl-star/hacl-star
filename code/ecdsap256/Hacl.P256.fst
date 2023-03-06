module Hacl.P256

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.Hash.Definitions

open Hacl.Impl.P256.Sign
open Hacl.Impl.P256.Verify

module S = Spec.P256

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"


let ecdsa_sign_p256_sha2 result mLen m privKey k =
  ecdsa_signature (S.Hash SHA2_256) result mLen m privKey k

let ecdsa_sign_p256_sha384 result mLen m privKey k =
  ecdsa_signature (S.Hash SHA2_384) result mLen m privKey k

let ecdsa_sign_p256_sha512 result mLen m privKey k =
  ecdsa_signature (S.Hash SHA2_512) result mLen m privKey k

let ecdsa_sign_p256_without_hash result mLen m privKey k =
  ecdsa_signature S.NoHash result mLen m privKey k


let ecdsa_verif_p256_sha2 mLen m pubKey r s =
  ecdsa_verification (S.Hash SHA2_256) pubKey r s mLen m

let ecdsa_verif_p256_sha384 mLen m pubKey r s =
  ecdsa_verification (S.Hash SHA2_384) pubKey r s mLen m

let ecdsa_verif_p256_sha512 mLen m pubKey r s =
  ecdsa_verification (S.Hash SHA2_512) pubKey r s mLen m

let ecdsa_verif_without_hash mLen m pubKey r s =
  ecdsa_verification S.NoHash pubKey r s mLen m


let validate_public_key pubKey =
  Hacl.Impl.P256.Point.validate_pubkey pubKey

let validate_private_key x =
  Hacl.Impl.P256.Point.isMoreThanZeroLessThanOrder x


let uncompressed_to_raw b result =
  Hacl.Impl.P256.Compression.decompressionNotCompressedForm b result

let compressed_to_raw b result =
  Hacl.Impl.P256.Compression.decompressionCompressedForm b result

let raw_to_uncompressed b result =
  Hacl.Impl.P256.Compression.compressionNotCompressedForm b result

let raw_to_compressed b result =
  Hacl.Impl.P256.Compression.compressionCompressedForm b result


let dh_initiator result scalar =
  Hacl.Impl.P256.DH.ecp256dh_i result scalar

let dh_responder result pubKey scalar =
  Hacl.Impl.P256.DH.ecp256dh_r result pubKey scalar
