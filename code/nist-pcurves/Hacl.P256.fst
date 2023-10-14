module Hacl.P256

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.Hash.Definitions
open Hacl.Hash.SHA2

open Hacl.Impl.PCurves.Sign
open Hacl.Impl.PCurves.Verify

module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module S = Spec.PCurves
module BN = Hacl.Impl.PCurves.Bignum
module P = Hacl.Impl.PCurves.Point

open Hacl.Impl.PCurves.Bignum.P256
open Hacl.Impl.PCurves.Constants.P256
open Hacl.Impl.PCurves.Field.P256
open Hacl.Impl.PCurves.Scalar.P256
open Hacl.Impl.PCurves.Finv.P256
open Hacl.Impl.PCurves.Qinv.P256
open Hacl.Impl.PCurves.Group.P256
open Hacl.Impl.PCurves.PrecompTable.P256
open Hacl.Impl.PCurves.PointMul.P256

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val msg_as_felem:
    alg:S.hash_alg_ecdsa
  -> msg_len:size_t{S.min_input_length alg (v msg_len)}
  -> msg:lbytes msg_len
  -> res:BN.felem ->
  Stack unit
  (requires fun h ->
    live h msg /\ live h res /\ disjoint msg res)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    (let hashM = S.hash_ecdsa alg (v msg_len) (as_seq h0 msg) in
    BN.as_nat h1 res = BSeq.nat_from_bytes_be (LSeq.sub hashM 0 32) % S.order))

inline_for_extraction noextract
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
  LowStar.Ignore.ignore msg_len;
  let mHash32 = sub mHash 0ul 32ul in
  BN.bn_from_bytes_be res mHash32;
  qmod_short res res;
  pop_frame ()

[@ CInline ]
val ecdsa_sign_msg_as_qelem:
    signature:lbuffer uint8 (2ul *. 32ul)
  -> m_q:BN.felem
  -> private_key:lbuffer uint8 32ul
  -> nonce:lbuffer uint8 32ul ->
  Stack bool
  (requires fun h ->
    live h signature /\ live h m_q /\ live h private_key /\ live h nonce /\
    disjoint signature m_q /\ disjoint signature private_key /\ disjoint signature nonce /\
    disjoint m_q private_key /\ disjoint m_q nonce /\
    BN.as_nat h m_q < S.order)
  (ensures fun h0 flag h1 -> modifies (loc signature |+| loc m_q) h0 h1 /\
    (let sgnt = S.ecdsa_sign_msg_as_qelem
      (BN.as_nat h0 m_q) (as_seq h0 private_key) (as_seq h0 nonce) in
     (flag <==> Some? sgnt) /\ (flag ==> (as_seq h1 signature == Some?.v sgnt))))

let ecdsa_sign_msg_as_qelem signature m_q private_key nonce =
  ecdsa_sign_msg_as_qelem
  #p256_params
  #p256_curve_constants
  #p256_bn_ops
  #p256_field_ops
  #p256_order_ops
  #p256_inv_sqrt
  #p256_point_ops
  #p256_precomp_tables
  #p256_point_mul_ops
  signature m_q private_key nonce
 
[@ CInline ]
val ecdsa_verify_msg_as_qelem:
    m_q:BN.felem
  -> public_key:lbuffer uint8 (2ul *. 32ul)
  -> signature_r:lbuffer uint8 32ul
  -> signature_s:lbuffer uint8 32ul ->
  Stack bool
  (requires fun h ->
    live h public_key /\ live h signature_r /\ live h signature_s /\ live h m_q /\
    BN.as_nat h m_q < S.order)
  (ensures fun h0 result h1 -> modifies0 h0 h1 /\
    result == S.ecdsa_verify_msg_as_qelem (BN.as_nat h0 m_q)
      (as_seq h0 public_key) (as_seq h0 signature_r) (as_seq h0 signature_s))

let ecdsa_verify_msg_as_qelem m_q public_key signature_r signature_s =
  ecdsa_verify_msg_as_qelem
  #p256_params
  #p256_curve_constants
  #p256_bn_ops
  #p256_field_ops
  #p256_order_ops
  #p256_inv_sqrt
  #p256_point_ops
  #p256_precomp_tables
  #p256_point_mul_ops
  m_q public_key signature_r signature_s

inline_for_extraction noextract
val ecdsa_signature: alg:S.hash_alg_ecdsa -> ecdsa_sign_p256_st alg
let ecdsa_signature alg signature msg_len msg private_key nonce =
  push_frame ();
  let m_q = BN.create_felem #p256_params in
  msg_as_felem alg msg_len msg m_q;
  let res = ecdsa_sign_msg_as_qelem signature m_q private_key nonce in
  pop_frame ();
  res


inline_for_extraction noextract
val ecdsa_verification: alg:S.hash_alg_ecdsa -> ecdsa_verify_p256_st alg
let ecdsa_verification alg msg_len msg public_key signature_r signature_s =
  push_frame ();
  let m_q = BN.create_felem #p256_params in
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
  let point_jac = P.create_point #p256_params in
  let res = P.load_point_vartime point_jac public_key in
  pop_frame ();
  res


let validate_private_key private_key =
  push_frame ();
  let bn_sk = BN.create_felem #p256_params in
  BN.bn_from_bytes_be bn_sk private_key;
  let res = Hacl.Impl.PCurves.Scalar.bn_is_lt_order_and_gt_zero_mask bn_sk in
  pop_frame ();
  Hacl.Bignum.Base.unsafe_bool_of_limb res


let uncompressed_to_raw pk pk_raw =
  Hacl.Impl.PCurves.Compression.uncompressed_to_raw pk pk_raw

let compressed_to_raw pk pk_raw =
  Hacl.Impl.PCurves.Compression.compressed_to_raw pk pk_raw

let raw_to_uncompressed pk_raw pk =
  Hacl.Impl.PCurves.Compression.raw_to_uncompressed pk_raw pk

let raw_to_compressed pk_raw pk =
  Hacl.Impl.PCurves.Compression.raw_to_compressed pk_raw pk


let dh_initiator public_key private_key =
  Hacl.Impl.PCurves.DH.ecp256dh_i
  #p256_params
  #p256_curve_constants
  #p256_bn_ops
  #p256_field_ops
  #p256_order_ops
  #p256_inv_sqrt
  #p256_point_ops
  #p256_precomp_tables
  #p256_point_mul_ops
  public_key private_key

let dh_responder shared_secret their_pubkey private_key =
  Hacl.Impl.PCurves.DH.ecp256dh_r
  #p256_params
  #p256_curve_constants
  #p256_bn_ops
  #p256_field_ops
  #p256_order_ops
  #p256_inv_sqrt
  #p256_point_ops
  #p256_precomp_tables
  #p256_point_mul_ops
  shared_secret their_pubkey private_key
