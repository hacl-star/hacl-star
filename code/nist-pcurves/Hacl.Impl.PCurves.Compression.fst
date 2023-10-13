module Hacl.Impl.PCurves.Compression

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.PCurves.Bignum
open Hacl.Impl.PCurves.Field
module P = Hacl.Impl.PCurves.Point

module S = Spec.PCurves
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

let uncompressed_to_raw {| cp:S.curve_params |} pk pk_raw =
  let pk0 = pk.(0ul) in
  if Lib.RawIntTypes.u8_to_UInt8 pk0 <> 0x04uy then false
  else begin
    copy pk_raw (sub pk 1ul (2ul *. size cp.bytes));
    true end

#push-options "--z3rlimit 200 --split_queries always"
let compressed_to_raw {| cp:S.curve_params |} {| curve_constants |} {| bn_ops |} {| field_ops |} {| order_ops |} {| curve_inv_sqrt|} pk pk_raw =
  push_frame ();
  let xa = create_felem #cp in
  let ya = create_felem #cp in
  let pk_xb = sub pk 1ul (size cp.bytes) in
  let b = P.aff_point_decompress_vartime xa ya pk in
  if b then begin
    let h0 = ST.get () in
    update_sub pk_raw 0ul (size cp.bytes) pk_xb;
    let h1 = ST.get () in
    FStar.Math.Lemmas.pow2_le_compat (8 * cp.bytes) (cp.bits);
    assert (as_nat h1 ya < pow2 (8 * cp.bytes));
    update_sub_f h1 pk_raw (size cp.bytes) (size cp.bytes)
      (fun h -> BSeq.nat_to_bytes_be cp.bytes (as_nat h1 ya))
      (fun _ -> bn_to_bytes_be (sub pk_raw (size cp.bytes) (size cp.bytes)) ya);
    let h2 = ST.get () in
    LSeq.eq_intro (as_seq h2 pk_raw)
      (LSeq.concat #_ #cp.bytes #cp.bytes (as_seq h0 pk_xb) (BSeq.nat_to_bytes_be cp.bytes (as_nat h0 ya))) end;
  pop_frame ();
  b
#pop-options

let raw_to_uncompressed {| cp:S.curve_params |} {| curve_constants |} {| bn_ops |} {| field_ops |} {| order_ops |} {| curve_inv_sqrt|} pk_raw pk =
  let h0 = ST.get () in
  pk.(0ul) <- u8 0x04;
  update_sub pk 1ul (2ul *. size cp.bytes) pk_raw;
  let h1 = ST.get () in
  LSeq.eq_intro (as_seq h1 pk) (S.pk_uncompressed_from_raw (as_seq h0 pk_raw))


inline_for_extraction noextract
val raw_to_compressed_get_pk0 {| cp:S.curve_params |} {| curve_constants |} {| bn_ops |} {| field_ops |} {| order_ops |} {| curve_inv_sqrt|}: f:lbuffer uint8 (size cp.bytes) -> Stack uint8
  (requires fun h -> live h f)
  (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
    v b == (if (BSeq.nat_from_bytes_be (as_seq h0 f) % 2 = 1) then 0x03 else 0x02))

let raw_to_compressed_get_pk0 {| cp:S.curve_params |} {| curve_constants |} {| bn_ops |} {| field_ops |} {| order_ops |} {| curve_inv_sqrt|} f =
  push_frame ();
  let bn_f = create_felem #cp in
  bn_from_bytes_be bn_f f;
  let is_odd_f = bn_is_odd bn_f in
  pop_frame ();
  to_u8 is_odd_f +! u8 0x02


let raw_to_compressed {| cp:S.curve_params |} {| curve_constants |} {| bn_ops |} {| field_ops |} {| order_ops |} {| curve_inv_sqrt|} pk_raw pk =
  let h0 = ST.get () in
  let pk_x = sub pk_raw 0ul (size cp.bytes) in
  let pk_y = sub pk_raw (size cp.bytes) (size cp.bytes) in
  pk.(0ul) <- raw_to_compressed_get_pk0 pk_y;
  update_sub pk 1ul (size cp.bytes) pk_x;
  let h1 = ST.get () in
  LSeq.eq_intro (as_seq h1 pk) (S.pk_compressed_from_raw (as_seq h0 pk_raw))
