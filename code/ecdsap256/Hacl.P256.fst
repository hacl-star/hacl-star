module Hacl.P256

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.Hash.Definitions
open Hacl.Hash.SHA2

open Hacl.Impl.P256.Sign
open Hacl.Impl.P256.Verify

module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module S = Spec.P256
module BN = Hacl.Impl.P256.Bignum
module P = Hacl.Impl.P256.Point

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val msg_as_felem:
    alg:S.hash_alg_ecdsa
  -> msg_len:size_t{v msg_len >= S.min_input_length alg}
  -> msg:lbytes msg_len
  -> res:BN.felem ->
  Stack unit
  (requires fun h ->
    live h msg /\ live h res /\ disjoint msg res)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    (let hashM = S.hash_ecdsa alg (v msg_len) (as_seq h0 msg) in
    BN.as_nat h1 res = BSeq.nat_from_bytes_be (LSeq.sub hashM 0 32) % S.order))

let msg_as_felem alg msg_len msg res =
  push_frame ();

  [@inline_let] let sz: size_t =
    match alg with
    | S.NoHash -> 32ul
    | S.Hash a -> Hacl.Hash.Definitions.hash_len a in

  let mHash = create sz (u8 0) in

  begin
  match alg with
    | S.NoHash -> copy mHash (sub msg 0ul 32ul)
    | S.Hash a -> match a with
      | SHA2_256 -> Hacl.Streaming.SHA2.hash_256 msg msg_len mHash
      | SHA2_384 -> Hacl.Streaming.SHA2.hash_384 msg msg_len mHash
      | SHA2_512 -> Hacl.Streaming.SHA2.hash_512 msg msg_len mHash
  end;

  let mHash32 = sub mHash 0ul 32ul in
  BN.bn_from_bytes_be4 res mHash32;
  Hacl.Impl.P256.Scalar.qmod_short res res;
  pop_frame ()


inline_for_extraction noextract
val ecdsa_signature: alg:S.hash_alg_ecdsa -> ecdsa_sign_p256_st alg
let ecdsa_signature alg signature msg_len msg private_key nonce =
  push_frame ();
  let m_q = BN.create_felem () in
  msg_as_felem alg msg_len msg m_q;
  let res = ecdsa_sign_msg_as_qelem signature m_q private_key nonce in
  pop_frame ();
  res


inline_for_extraction noextract
val ecdsa_verification: alg:S.hash_alg_ecdsa -> ecdsa_verify_p256_st alg
let ecdsa_verification alg msg_len msg public_key signature_r signature_s =
  push_frame ();
  let m_q = BN.create_felem () in
  msg_as_felem alg msg_len msg m_q;
  let res = ecdsa_verify_msg_as_qelem m_q public_key signature_r signature_s in
  pop_frame ();
  res


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
