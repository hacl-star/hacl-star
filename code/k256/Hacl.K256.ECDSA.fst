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

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let ecdsa_sign_hashed_msg r s m private_key k =
  SK.ecdsa_sign_hashed_msg r s m private_key k


let ecdsa_verify_hashed_msg m public_key r s =
  VK.ecdsa_verify_hashed_msg m public_key r s


let ecdsa_sign_sha256 r s msg_len msg private_key k =
  push_frame ();
  let mHash = create 32ul (u8 0) in
  Hacl.Hash.SHA2.hash_256 msg msg_len mHash;
  let b = ecdsa_sign_hashed_msg r s mHash private_key k in
  pop_frame ();
  b


let ecdsa_verify_sha256 msg_len msg public_key r s =
  push_frame ();
  let mHash = create 32ul (u8 0) in
  Hacl.Hash.SHA2.hash_256 msg msg_len mHash;
  let b = ecdsa_verify_hashed_msg mHash public_key r s in
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
  let pk0 = pk.(0ul) in
  if not (Lib.RawIntTypes.u8_to_UInt8 pk0 = 0x02uy ||
    Lib.RawIntTypes.u8_to_UInt8 pk0 = 0x03uy) then false
  else begin
    let pk_xb = sub pk 1ul 32ul in
    let is_pk_y_odd = Lib.RawIntTypes.u8_to_UInt8 pk0 = 0x03uy in
    let pk_yb = sub pk_raw 32ul 32ul in
    let b = P.recover_y_bytes_vartime pk_yb pk_xb is_pk_y_odd in
    let h0 = ST.get () in
    update_sub pk_raw 0ul 32ul pk_xb;
    let h1 = ST.get () in
    LSeq.eq_intro (as_seq h1 pk_raw) (LSeq.concat (as_seq h0 pk_xb) (as_seq h0 pk_yb));
    b end


inline_for_extraction noextract
val is_nat_from_bytes_be_odd_vartime: f:lbytes 32ul -> Stack bool
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
