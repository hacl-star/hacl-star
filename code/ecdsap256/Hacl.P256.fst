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


let ecdsa_sign_p256_sha2 signature msg_len msg private_key nonce =
  ecdsa_signature (S.Hash SHA2_256) signature msg_len msg private_key nonce

let ecdsa_sign_p256_sha384 signature msg_len msg private_key nonce =
  ecdsa_signature (S.Hash SHA2_384) signature msg_len msg private_key nonce

let ecdsa_sign_p256_sha512 signature msg_len msg private_key nonce =
  ecdsa_signature (S.Hash SHA2_512) signature msg_len msg private_key nonce

let ecdsa_sign_p256_without_hash signature msg_len msg private_key nonce =
  ecdsa_signature S.NoHash signature msg_len msg private_key nonce


let ecdsa_verif_p256_sha2 msg_len msg public_key signature_r signature_s =
  ecdsa_verification (S.Hash SHA2_256) public_key signature_r signature_s msg_len msg

let ecdsa_verif_p256_sha384 msg_len msg public_key signature_r signature_s =
  ecdsa_verification (S.Hash SHA2_384) public_key signature_r signature_s msg_len msg

let ecdsa_verif_p256_sha512 msg_len msg public_key signature_r signature_s =
  ecdsa_verification (S.Hash SHA2_512) public_key signature_r signature_s msg_len msg

let ecdsa_verif_without_hash msg_len msg public_key signature_r signature_s =
  ecdsa_verification S.NoHash public_key signature_r signature_s msg_len msg


let validate_public_key public_key =
  Hacl.Impl.P256.Point.validate_pubkey public_key

let validate_private_key private_key =
  Hacl.Impl.P256.Point.isMoreThanZeroLessThanOrder private_key


let uncompressed_to_raw b result =
  Hacl.Impl.P256.Compression.decompressionNotCompressedForm b result

let compressed_to_raw b result =
  Hacl.Impl.P256.Compression.decompressionCompressedForm b result

let raw_to_uncompressed b result =
  Hacl.Impl.P256.Compression.compressionNotCompressedForm b result

let raw_to_compressed b result =
  Hacl.Impl.P256.Compression.compressionCompressedForm b result


let dh_initiator public_key private_key =
  Hacl.Impl.P256.DH.ecp256dh_i public_key private_key

let dh_responder shared_secret their_pubkey private_key =
  Hacl.Impl.P256.DH.ecp256dh_r shared_secret their_pubkey private_key
