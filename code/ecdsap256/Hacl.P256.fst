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
module BN = Hacl.Impl.P256.Bignum
module P = Hacl.Impl.P256.Point

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
  ecdsa_verification (S.Hash SHA2_256) msg_len msg public_key signature_r signature_s

let ecdsa_verif_p256_sha384 msg_len msg public_key signature_r signature_s =
  ecdsa_verification (S.Hash SHA2_384) msg_len msg public_key signature_r signature_s

let ecdsa_verif_p256_sha512 msg_len msg public_key signature_r signature_s =
  ecdsa_verification (S.Hash SHA2_512) msg_len msg public_key signature_r signature_s

let ecdsa_verif_without_hash msg_len msg public_key signature_r signature_s =
  ecdsa_verification S.NoHash msg_len msg public_key signature_r signature_s


let validate_public_key public_key =
  push_frame ();
  let point_jac = P.create_point () in
  let res = P.load_point_vartime point_jac public_key in
  pop_frame ();
  res


let validate_private_key private_key =
  push_frame ();
  let bn_sk = BN.create_felem () in
  BN.bn_from_bytes_be4 bn_sk private_key;
  let res = Hacl.Impl.P256.Scalar.bn_is_lt_order_and_gt_zero_mask4 bn_sk in
  pop_frame ();
  Hacl.Bignum.Base.unsafe_bool_of_limb res


let uncompressed_to_raw pk pk_raw =
  Hacl.Impl.P256.Compression.uncompressed_to_raw pk pk_raw

let compressed_to_raw pk pk_raw =
  Hacl.Impl.P256.Compression.compressed_to_raw pk pk_raw

let raw_to_uncompressed pk_raw pk =
  Hacl.Impl.P256.Compression.raw_to_uncompressed pk_raw pk

let raw_to_compressed pk_raw pk =
  Hacl.Impl.P256.Compression.raw_to_compressed pk_raw pk


let dh_initiator public_key private_key =
  Hacl.Impl.P256.DH.ecp256dh_i public_key private_key

let dh_responder shared_secret their_pubkey private_key =
  Hacl.Impl.P256.DH.ecp256dh_r shared_secret their_pubkey private_key
