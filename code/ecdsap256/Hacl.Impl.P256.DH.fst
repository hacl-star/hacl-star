module Hacl.Impl.P256.DH

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Scalar
open Hacl.Impl.P256.Point
open Hacl.Impl.P256.PointMul

module S = Spec.P256
module BSeq = Lib.ByteSequence

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val make_sk_as_qelem: res:felem -> sk:lbuffer uint8 32ul -> Stack uint64
  (requires fun h ->
    live h res /\ live h sk /\ disjoint res sk)
  (ensures fun h0 m h1 -> modifies (loc res) h0 h1 /\
   (let sk_nat = BSeq.nat_from_bytes_be (as_seq h0 sk) in
    let is_sk_valid = 0 < sk_nat && sk_nat < S.order in
    (v m = ones_v U64 \/ v m = 0) /\ (v m = ones_v U64) = is_sk_valid /\
    as_nat h1 res == (if is_sk_valid then sk_nat else 1)))

let make_sk_as_qelem res sk =
  push_frame ();
  bn_from_bytes_be4 res sk;
  let is_sk_valid = bn_is_lt_order_and_gt_zero_mask4 res in

  let oneq = create_felem () in
  bn_set_one4 oneq;
  let h0 = ST.get () in
  Lib.ByteBuffer.buf_mask_select res oneq is_sk_valid res;
  let h1 = ST.get () in
  assert (as_seq h1 res == (if (v is_sk_valid = 0) then as_seq h0 oneq else as_seq h0 res));
  pop_frame ();
  is_sk_valid


[@CInline]
let ecp256dh_i public_key private_key =
  push_frame ();
  let tmp = create 16ul (u64 0) in
  let sk = sub tmp 0ul 4ul in
  let pk = sub tmp 4ul 12ul in

  let is_sk_valid = make_sk_as_qelem sk private_key in
  point_mul_g pk sk;
  point_store public_key pk;
  pop_frame ();
  Hacl.Bignum.Base.unsafe_bool_of_limb is_sk_valid


inline_for_extraction noextract
val ecp256dh_r_: is_pk_valid:bool -> ss:lbuffer uint8 64ul -> pk:point -> sk:felem -> Stack unit
  (requires fun h ->
    live h ss /\ live h pk /\ live h sk /\
    disjoint ss pk /\ disjoint ss sk /\ disjoint pk sk /\
    as_nat h sk < S.order /\ (is_pk_valid ==> point_inv h pk))
  (ensures fun  h0 _ h1 -> modifies (loc ss) h0 h1 /\
    as_seq h1 ss == (if is_pk_valid
    then S.point_store (S.point_mul (as_nat h0 sk) (from_mont_point (as_point_nat h0 pk)))
    else as_seq h0 ss))

let ecp256dh_r_ is_pk_valid ss pk sk =
  push_frame ();
  let ss_proj = create_point () in
  if is_pk_valid then begin
    point_mul ss_proj sk pk;
    point_store ss ss_proj end;
  pop_frame ()


[@CInline]
let ecp256dh_r shared_secret their_pubkey private_key =
  push_frame ();
  let tmp = create 16ul (u64 0) in
  let sk = sub tmp 0ul 4ul in
  let pk = sub tmp 4ul 12ul in

  let is_pk_valid = load_point_vartime pk their_pubkey in
  let is_sk_valid = make_sk_as_qelem sk private_key in
  ecp256dh_r_ is_pk_valid shared_secret pk sk;
  pop_frame ();
  Hacl.Bignum.Base.unsafe_bool_of_limb is_sk_valid && is_pk_valid
