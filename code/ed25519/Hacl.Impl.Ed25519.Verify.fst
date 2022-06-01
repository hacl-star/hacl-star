module Hacl.Impl.Ed25519.Verify

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module BSeq = Lib.ByteSequence

open Hacl.Bignum25519
module F51 = Hacl.Impl.Ed25519.Field51
module PM = Hacl.Impl.Ed25519.Ladder

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let point_inv_full_t (h:mem) (p:point) =
  F51.point_inv_t h p /\ PM.inv_ext_point (as_seq h p)


inline_for_extraction noextract
val verify_all_valid_hb (sb hb:lbuffer uint8 32ul) (a' r':point) : Stack bool
  (requires fun h ->
    live h sb /\ live h hb /\ live h a' /\ live h r' /\
    point_inv_full_t h a' /\ point_inv_full_t h r')
  (ensures fun h0 z h1 -> modifies0 h0 h1 /\
    (z == Spec.Ed25519.(
      let exp_d = point_negate_mul_double_g (as_seq h0 sb) (as_seq h0 hb) (F51.point_eval h0 a') in
      point_equal exp_d (F51.point_eval h0 r'))))

let verify_all_valid_hb sb hb a' r' =
  push_frame ();
  let exp_d = create 20ul (u64 0) in
  PM.point_negate_mul_double_g_vartime exp_d sb hb a';
  let b = Hacl.Impl.Ed25519.PointEqual.point_equal exp_d r' in
  pop_frame ();
  b


inline_for_extraction noextract
val verify_sb: sb:lbuffer uint8 32ul -> Stack bool
  (requires fun h -> live h sb)
  (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
    (b <==> (BSeq.nat_from_bytes_le (as_seq h0 sb) >= Spec.Ed25519.q)))

let verify_sb sb =
  push_frame ();
  let tmp = create 5ul (u64 0) in
  Hacl.Impl.Load56.load_32_bytes tmp sb;
  let b = Hacl.Impl.Ed25519.PointEqual.gte_q tmp in
  pop_frame ();
  b


inline_for_extraction noextract
val verify_valid_pk_rs:
    public_key:lbuffer uint8 32ul
  -> msg_len:size_t
  -> msg:lbuffer uint8 msg_len
  -> signature:lbuffer uint8 64ul
  -> a':point
  -> r':point ->
  Stack bool
    (requires fun h ->
      live h public_key /\ live h msg /\ live h signature /\ live h a' /\ live h r' /\
      (Some? (Spec.Ed25519.point_decompress (as_seq h public_key))) /\ point_inv_full_t h a' /\
      (F51.point_eval h a' == Some?.v (Spec.Ed25519.point_decompress (as_seq h public_key))) /\
      (Some? (Spec.Ed25519.point_decompress (as_seq h (gsub signature 0ul 32ul)))) /\ point_inv_full_t h r' /\
      (F51.point_eval h r' == Some?.v (Spec.Ed25519.point_decompress (as_seq h (gsub signature 0ul 32ul)))))
    (ensures fun h0 z h1 -> modifies0 h0 h1 /\
      z == Spec.Ed25519.verify (as_seq h0 public_key) (as_seq h0 msg) (as_seq h0 signature))

let verify_valid_pk_rs public_key msg_len msg signature a' r' =
  push_frame ();
  let hb = create 32ul (u8 0) in
  let rs = sub signature 0ul 32ul in
  let sb = sub signature 32ul 32ul in

  let b = verify_sb sb in
  let res =
    if b then false
    else begin
      Hacl.Impl.SHA512.ModQ.store_sha512_modq_pre_pre2 hb rs public_key msg_len msg;
      verify_all_valid_hb sb hb a' r' end in
  pop_frame ();
  res


inline_for_extraction noextract
val verify_valid_pk:
    public_key:lbuffer uint8 32ul
  -> msg_len:size_t
  -> msg:lbuffer uint8 msg_len
  -> signature:lbuffer uint8 64ul
  -> a':point ->
  Stack bool
    (requires fun h ->
      live h public_key /\ live h msg /\ live h signature /\ live h a' /\
      (Some? (Spec.Ed25519.point_decompress (as_seq h public_key))) /\ point_inv_full_t h a' /\
      (F51.point_eval h a' == Some?.v (Spec.Ed25519.point_decompress (as_seq h public_key))))
    (ensures fun h0 z h1 -> modifies0 h0 h1 /\
      z == Spec.Ed25519.verify (as_seq h0 public_key) (as_seq h0 msg) (as_seq h0 signature))

let verify_valid_pk public_key msg_len msg signature a' =
  push_frame ();
  let r' = create 20ul (u64 0) in
  let rs = sub signature 0ul 32ul in
  let h0 = ST.get () in
  Spec.Ed25519.Lemmas.point_decompress_lemma (as_seq h0 rs);
  let b' = Hacl.Impl.Ed25519.PointDecompress.point_decompress r' rs in
  let res = if b' then verify_valid_pk_rs public_key msg_len msg signature a' r' else false in
  pop_frame ();
  res


inline_for_extraction noextract
val verify:
    public_key:lbuffer uint8 32ul
  -> msg_len:size_t
  -> msg:lbuffer uint8 msg_len
  -> signature:lbuffer uint8 64ul ->
  Stack bool
    (requires fun h ->
      live h public_key /\ live h msg /\ live h signature)
    (ensures fun h0 z h1 -> modifies0 h0 h1 /\
      z == Spec.Ed25519.verify (as_seq h0 public_key) (as_seq h0 msg) (as_seq h0 signature))

let verify public_key msg_len msg signature =
  push_frame ();
  let a' = create 20ul (u64 0) in
  let h0 = ST.get () in
  Spec.Ed25519.Lemmas.point_decompress_lemma (as_seq h0 public_key);
  let b = Hacl.Impl.Ed25519.PointDecompress.point_decompress a' public_key in
  let res = if b then verify_valid_pk public_key msg_len msg signature a' else false in
  pop_frame ();
  res
