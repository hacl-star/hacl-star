module Hacl.Impl.Ed25519.Sign

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module BSeq = Lib.ByteSequence
module LSeq = Lib.Sequence

module F51 = Hacl.Impl.Ed25519.Field51
module BQ = Hacl.Impl.BignumQ
module BD = Hacl.Bignum.Definitions

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val point_mul_g_compress (out s:lbuffer uint8 32ul) : Stack unit
  (requires fun h ->
    live h out /\ live h s /\ disjoint s out)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.Ed25519.point_compress (Spec.Ed25519.point_mul_g (as_seq h0 s)))

[@CInline]
let point_mul_g_compress out s =
  push_frame ();
  let tmp = create 20ul (u64 0) in
  Hacl.Impl.Ed25519.Ladder.point_mul_g tmp s;
  Hacl.Impl.Ed25519.PointCompress.point_compress out tmp;
  pop_frame ()


inline_for_extraction noextract
val sign_compute_s (r hs:lbuffer uint64 4ul) (a s:lbuffer uint8 32ul) : Stack unit
  (requires fun h ->
    live h r /\ live h hs /\ live h a /\ live h s /\
    disjoint s r /\ disjoint s hs /\ disjoint s a /\
    BD.bn_v h r < Spec.Ed25519.q /\ BD.bn_v h hs < Spec.Ed25519.q)
  (ensures  fun h0 _ h1 -> modifies (loc s) h0 h1 /\
    as_seq h1 s == BSeq.nat_to_bytes_le 32 ((BD.bn_v h0 r +
      (BD.bn_v h0 hs * BSeq.nat_from_bytes_le (as_seq h0 a)) % Spec.Ed25519.q) % Spec.Ed25519.q))

let sign_compute_s r hs a s =
  push_frame ();
  let aq = create 4ul (u64 0) in
  BQ.load_32_bytes aq a;
  BQ.mul_add_modq hs aq r aq;
  BQ.store_32_bytes s aq;
  pop_frame ()


inline_for_extraction noextract
val sign_expanded:
    signature:lbuffer uint8 64ul
  -> expanded_keys:lbuffer uint8 96ul
  -> msg_len:size_t
  -> msg:lbuffer uint8 msg_len ->
  Stack unit
    (requires fun h ->
      live h signature /\ live h msg /\ live h expanded_keys /\
      disjoint signature msg /\ disjoint signature expanded_keys)
    (ensures  fun h0 _ h1 -> modifies (loc signature) h0 h1 /\
      as_seq h1 signature == Spec.Ed25519.sign_expanded
        (as_seq h0 (gsub expanded_keys 0ul 32ul))
        (as_seq h0 (gsub expanded_keys 32ul 32ul))
        (as_seq h0 (gsub expanded_keys 64ul 32ul))
        (as_seq h0 msg))

let sign_expanded signature expanded_keys msg_len msg =
  push_frame ();
  let rs = sub signature 0ul 32ul in
  let ss = sub signature 32ul 32ul in

  let rq = create 4ul (u64 0) in
  let hq = create 4ul (u64 0) in
  let rb = create 32ul (u8 0) in

  // expanded_keys = [ public_key; s; prefix ]
  let public_key = sub expanded_keys  0ul 32ul in
  let s          = sub expanded_keys 32ul 32ul in
  let prefix     = sub expanded_keys 64ul 32ul in

  Hacl.Impl.SHA512.ModQ.store_sha512_modq_pre rb rq prefix msg_len msg;
  point_mul_g_compress rs rb;
  Hacl.Impl.SHA512.ModQ.sha512_modq_pre_pre2 hq rs public_key msg_len msg;
  sign_compute_s rq hq s ss;
  let h1 = ST.get () in
  LSeq.eq_intro (as_seq h1 signature)
    (Spec.Ed25519.sign_expanded (as_seq h1 public_key) (as_seq h1 s) (as_seq h1 prefix) (as_seq h1 msg));
  pop_frame ()
