module Hacl.K256.ECDSA

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module S = Spec.K256
module BDL = Hacl.Spec.K256.Field52.Definitions.Lemmas

module P = Hacl.Impl.K256.Point
module SK = Hacl.Impl.K256.Sign
module VK = Hacl.Impl.K256.Verify

open Hacl.K256.Field
open Hacl.K256.Scalar

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let ecdsa_sign_hashed_msg signature msgHash private_key nonce =
  SK.ecdsa_sign_hashed_msg signature msgHash private_key nonce


let ecdsa_sign_sha256 signature msg_len msg private_key nonce =
  push_frame ();
  let msgHash = create 32ul (u8 0) in
  Hacl.Streaming.SHA2.hash_256 msgHash msg msg_len;
  let b = ecdsa_sign_hashed_msg signature msgHash private_key nonce in
  pop_frame ();
  b


let ecdsa_verify_hashed_msg m public_key signature =
  VK.ecdsa_verify_hashed_msg m public_key signature


let ecdsa_verify_sha256 msg_len msg public_key signature =
  push_frame ();
  let mHash = create 32ul (u8 0) in
  Hacl.Streaming.SHA2.hash_256 mHash msg msg_len;
  let b = ecdsa_verify_hashed_msg mHash public_key signature in
  pop_frame ();
  b

///  Low-S normalization

let secp256k1_ecdsa_signature_normalize signature =
  push_frame ();
  let s_q = create_qelem () in
  let s = sub signature 32ul 32ul in
  let is_sk_valid = load_qelem_vartime s_q s in
  let b =
    if not is_sk_valid then false
    else begin
      let is_sk_lt_q_halved = is_qelem_le_q_halved_vartime s_q in
      qnegate_conditional_vartime s_q (not is_sk_lt_q_halved);

      let h1 = ST.get () in
      update_sub_f h1 signature 32ul 32ul
        (fun h -> BSeq.nat_to_bytes_be 32 (qas_nat h1 s_q))
        (fun _ -> store_qelem (sub signature 32ul 32ul) s_q);
      true end in
  pop_frame ();
  b


let secp256k1_ecdsa_is_signature_normalized signature =
  push_frame ();
  let s_q = create_qelem () in
  let s = sub signature 32ul 32ul in
  let is_s_valid = load_qelem_vartime s_q s in
  let is_s_lt_q_halved = is_qelem_le_q_halved_vartime s_q in
  pop_frame ();
  is_s_valid && is_s_lt_q_halved


let secp256k1_ecdsa_sign_hashed_msg signature msgHash private_key nonce =
  let b = ecdsa_sign_hashed_msg signature msgHash private_key nonce in
  if b then secp256k1_ecdsa_signature_normalize signature else false


let secp256k1_ecdsa_sign_sha256 signature msg_len msg private_key nonce =
  push_frame ();
  let msgHash = create 32ul (u8 0) in
  Hacl.Streaming.SHA2.hash_256 msgHash msg msg_len;
  let b = secp256k1_ecdsa_sign_hashed_msg signature msgHash private_key nonce in
  pop_frame ();
  b


let secp256k1_ecdsa_verify_hashed_msg msgHash public_key signature =
  let is_s_normalized = secp256k1_ecdsa_is_signature_normalized signature in
  if not is_s_normalized then false
  else ecdsa_verify_hashed_msg msgHash public_key signature


let secp256k1_ecdsa_verify_sha256 msg_len msg public_key signature =
  push_frame ();
  let mHash = create 32ul (u8 0) in
  Hacl.Streaming.SHA2.hash_256 mHash msg msg_len;
  let b = secp256k1_ecdsa_verify_hashed_msg mHash public_key signature in
  pop_frame ();
  b


///  Parsing and Serializing public keys

let public_key_uncompressed_to_raw pk_raw pk =
  let pk0 = pk.(0ul) in
  if Lib.RawIntTypes.u8_to_UInt8 pk0 <> 0x04uy then false
  else begin
    copy pk_raw (sub pk 1ul 64ul);
    true end


let public_key_uncompressed_from_raw pk pk_raw =
  let h0 = ST.get () in
  pk.(0ul) <- u8 0x04;
  update_sub pk 1ul 64ul pk_raw;
  let h1 = ST.get () in
  LSeq.eq_intro (as_seq h1 pk) (S.pk_uncompressed_from_raw (as_seq h0 pk_raw))


let public_key_compressed_to_raw pk_raw pk =
  push_frame ();
  let xa = create_felem () in
  let ya = create_felem () in
  let b = P.aff_point_decompress_vartime xa ya pk in
  let pk_xb = sub pk 1ul 32ul in

  if b then begin
    let h0 = ST.get () in
    update_sub pk_raw 0ul 32ul pk_xb;
    let h1 = ST.get () in
    update_sub_f h1 pk_raw 32ul 32ul
      (fun h -> BSeq.nat_to_bytes_be 32 (feval h1 ya))
      (fun _ -> store_felem (sub pk_raw 32ul 32ul) ya);
    let h2 = ST.get () in
    LSeq.eq_intro (as_seq h2 pk_raw)
      (LSeq.concat #_ #32 #32(as_seq h0 pk_xb) (BSeq.nat_to_bytes_be 32 (feval h0 ya))) end;
  pop_frame ();
  b


inline_for_extraction noextract
val is_nat_from_bytes_be_odd_vartime: f:lbuffer uint8 32ul -> Stack bool
  (requires fun h -> live h f)
  (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
    b == (BSeq.nat_from_bytes_be (as_seq h0 f) % 2 = 1))

let is_nat_from_bytes_be_odd_vartime f =
  let h0 = ST.get () in
  let x0 = f.(31ul) in
  BDL.lemma_nat_from_bytes_be_mod2 (as_seq h0 f);
  [@inline_let]
  let is_odd_m = x0 &. u8 1 in
  mod_mask_lemma x0 1ul;
  assert (v (mod_mask #U8 #SEC 1ul) == v (u8 1));
  assert_norm (pow2 1 = 2);
  assert (v is_odd_m = BSeq.nat_from_bytes_be (as_seq h0 f) % 2);
  Lib.RawIntTypes.u8_to_UInt8 is_odd_m =. 1uy


let public_key_compressed_from_raw pk pk_raw =
  let h0 = ST.get () in
  let pk_x = sub pk_raw 0ul 32ul in
  let pk_y = sub pk_raw 32ul 32ul in
  let is_pk_y_odd = is_nat_from_bytes_be_odd_vartime pk_y in
  pk.(0ul) <- if is_pk_y_odd then u8 0x03 else u8 0x02;
  update_sub pk 1ul 32ul pk_x;
  let h1 = ST.get () in
  LSeq.eq_intro (as_seq h1 pk) (S.pk_compressed_from_raw (as_seq h0 pk_raw))


let is_public_key_valid public_key =
  push_frame ();
  let p = P.create_point () in
  let is_pk_valid = P.load_point_vartime p public_key in
  pop_frame ();
  is_pk_valid

module BB = Hacl.Bignum.Base
module PM = Hacl.Impl.K256.PointMul

let is_private_key_valid private_key =
  push_frame ();
  let s_q = create_qelem () in
  let res = load_qelem_check s_q private_key in
  pop_frame ();
  BB.unsafe_bool_of_limb res


let secret_to_public public_key private_key =
  push_frame ();
  let tmp = create 19ul (u64 0) in
  let pk = sub tmp 0ul 15ul in
  let sk = sub tmp 15ul 4ul in

  let is_sk_valid = load_qelem_conditional sk private_key in
  PM.point_mul_g pk sk; // pk = [sk]G
  P.point_store public_key pk;
  pop_frame ();
  BB.unsafe_bool_of_limb is_sk_valid


let ecdh shared_secret their_pubkey private_key =
  push_frame ();
  let tmp = create 34ul (u64 0) in
  let pk = sub tmp 0ul 15ul in
  let ss = sub tmp 15ul 15ul in
  let sk = sub tmp 30ul 4ul in

  let is_pk_valid = P.load_point_vartime pk their_pubkey in
  let is_sk_valid = load_qelem_conditional sk private_key in

  if is_pk_valid then begin
    PM.point_mul ss sk pk;
    P.point_store shared_secret ss end;
  pop_frame ();
  BB.unsafe_bool_of_limb is_sk_valid && is_pk_valid
