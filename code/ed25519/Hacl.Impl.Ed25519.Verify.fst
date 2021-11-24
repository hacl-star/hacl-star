module Hacl.Impl.Ed25519.Verify

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum25519

module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module F51 = Hacl.Impl.Ed25519.Field51
module PM = Hacl.Impl.Ed25519.Ladder

#reset-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val verify_step_1:
    r:lbuffer uint8 32ul
  -> len:size_t{v len + 64 <= max_size_t}
  -> msg:lbuffer uint8 len
  -> rs:lbuffer uint8 32ul
  -> public:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h ->
      live h r /\ live h msg /\ live h rs /\ live h public /\
      disjoint msg r /\ disjoint rs r /\ disjoint public r)
    (ensures fun h0 _ h1 -> modifies (loc r) h0 h1 /\
     as_seq h1 r == BSeq.nat_to_bytes_le 32 (
      Spec.Ed25519.sha512_modq (64 + v len)
        (LSeq.concat #uint8 #64 #(v len)
          (LSeq.concat #uint8 #32 #32
            (as_seq h0 rs)
            (as_seq h0 public))
          (as_seq h0 msg)
        ))
    )
let verify_step_1 r msg len rs public =
  push_frame();
  let r' = create 5ul (u64 0) in
  Hacl.Impl.SHA512.ModQ.sha512_modq_pre_pre2 r' rs public msg len;
  Hacl.Impl.Store56.store_56 r r';
  pop_frame()


inline_for_extraction noextract
val verify_step_2:
    s:lbuffer uint8 32ul
  -> h':lbuffer uint8 32ul
  -> a':point
  -> tmp:lbuffer uint64 40ul ->
  Stack unit
    (requires fun h ->
      live h s  /\ live h h' /\ live h a' /\ live h tmp /\
      disjoint tmp h' /\ disjoint tmp s /\ disjoint tmp a' /\
      F51.point_inv_t h a' /\ PM.inv_ext_point (as_seq h a')
    )
    (ensures fun h0 _ h1 -> modifies (loc tmp) h0 h1 /\
     (let exp_d = gsub tmp 20ul 20ul in
      F51.point_inv_t h1 exp_d /\ PM.inv_ext_point (as_seq h1 exp_d) /\
      F51.point_eval h1 exp_d ==
      Spec.Ed25519.(point_negate_mul_double_g (as_seq h0 s) (as_seq h0 h') (F51.point_eval h0 a'))))

let verify_step_2 s h' a' tmp =
  let a_neg = sub tmp 0ul 20ul in
  let exp_d = sub tmp 20ul 20ul in
  let h0 = ST.get () in

  Spec.Ed25519.Lemmas.to_aff_point_negate (PM.refl_ext_point (as_seq h0 a'));
  Hacl.Impl.Ed25519.PointNegate.point_negate a' a_neg;
  Hacl.Impl.Ed25519.Ladder.point_mul_g_double_vartime exp_d s h' a_neg


#push-options "--z3rlimit 150"
inline_for_extraction noextract
val verify_step_3:
    s:lbuffer uint8 32ul
  -> h':lbuffer uint8 32ul
  -> a':point
  -> r':point ->
  Stack bool
    (requires fun h ->
      live h s  /\ live h h' /\ live h a' /\ live h r' /\
      disjoint a' r' /\
      F51.point_inv_t h a' /\ PM.inv_ext_point (as_seq h a') /\
      F51.point_inv_t h r' /\ PM.inv_ext_point (as_seq h r')
    )
    (ensures fun h0 z h1 -> modifies0 h0 h1 /\
      (z == Spec.Ed25519.(
        let exp_d = point_negate_mul_double_g (as_seq h0 s) (as_seq h0 h') (F51.point_eval h0 a') in
        point_equal exp_d (F51.point_eval h0 r')))
    )
let verify_step_3 s h' a' r' =
  push_frame();
  let tmp = create 40ul (u64 0) in
  verify_step_2 s h' a' tmp;
  let exp_d = sub tmp 20ul 20ul in
  let b = Hacl.Impl.Ed25519.PointEqual.point_equal exp_d r' in
  pop_frame();
  b


inline_for_extraction noextract
val verify_step4:
    public:lbuffer uint8 32ul
  -> len:size_t{v len + 64 <= max_size_t}
  -> msg:lbuffer uint8 len
  -> signature:lbuffer uint8 64ul
  -> tmp:lbuffer uint64 45ul
  -> tmp':lbuffer uint8 32ul ->
  Stack bool
    (requires fun h ->
      live h public /\ live h msg /\ live h signature /\ live h tmp /\ live h tmp' /\
      disjoint tmp public /\ disjoint tmp msg /\ disjoint tmp signature /\
      disjoint tmp tmp' /\ disjoint tmp' signature /\ disjoint tmp' public /\ disjoint tmp' msg /\
      F51.point_inv_t h (gsub tmp 0ul 20ul) /\ PM.inv_ext_point (as_seq h (gsub tmp 0ul 20ul)) /\
      F51.point_inv_t h (gsub tmp 20ul 20ul) /\ PM.inv_ext_point (as_seq h (gsub tmp 20ul 20ul)) /\
      (Some? (Spec.Ed25519.point_decompress (as_seq h public))) /\
      (F51.point_eval h (gsub tmp 0ul 20ul) == Some?.v (Spec.Ed25519.point_decompress (as_seq h public))) /\
      (Some? (Spec.Ed25519.point_decompress (as_seq h (gsub signature 0ul 32ul)))) /\
      (F51.point_eval h (gsub tmp 20ul 20ul) == Some?.v (Spec.Ed25519.point_decompress (as_seq h (gsub signature 0ul 32ul))))
    )
    (ensures fun h0 z h1 -> modifies (loc tmp |+| loc tmp') h0 h1 /\
      z == Spec.Ed25519.verify (as_seq h0 public) (as_seq h0 msg) (as_seq h0 signature)
    )

#push-options "--z3rlimit 200"

let verify_step4 public len msg signature tmp tmp' =
  let rs = sub signature 0ul 32ul in
  let a' = sub tmp 0ul  20ul in
  let r' = sub tmp 20ul 20ul in
  let s  = sub tmp 40ul 5ul  in
  (**) let h0 = ST.get() in
  Hacl.Impl.Load56.load_32_bytes s (sub signature 32ul 32ul);
  let b'' = Hacl.Impl.Ed25519.PointEqual.gte_q s in
  if b'' then false
  else (
    verify_step_1 tmp' len msg rs public;
    (**) BSeq.lemma_nat_from_to_bytes_le_preserves_value (LSeq.slice #uint8 #64 (as_seq h0 signature) 32 64) 32;
    verify_step_3 (sub signature 32ul 32ul) tmp' a' r')


inline_for_extraction noextract
val verify_step5:
    public:lbuffer uint8 32ul
  -> len:size_t{v len + 64 <= max_size_t}
  -> msg:lbuffer uint8 len
  -> signature:lbuffer uint8 64ul
  -> tmp:lbuffer uint64 45ul
  -> tmp':lbuffer uint8 32ul ->
  Stack bool
    (requires fun h ->
      live h public /\ live h msg /\ live h signature /\ live h tmp /\ live h tmp' /\
      F51.point_inv_t h (gsub tmp 0ul 20ul) /\ F51.point_inv_t h (gsub tmp 20ul 20ul) /\
      disjoint tmp public /\ disjoint tmp msg /\ disjoint tmp signature /\
      disjoint tmp tmp' /\ disjoint tmp' signature /\ disjoint tmp' public /\ disjoint tmp' msg
    )
    (ensures fun h0 z h1 -> modifies (loc tmp |+| loc tmp') h0 h1 /\
      z == Spec.Ed25519.verify (as_seq h0 public) (as_seq h0 msg) (as_seq h0 signature)
    )

let verify_step5 public msg len signature tmp tmp' =
  let a' = sub tmp 0ul  20ul in
  let r' = sub tmp 20ul 20ul in
  let b = Hacl.Impl.Ed25519.PointDecompress.point_decompress a' public in
  let h0 = ST.get () in
  Spec.Ed25519.Lemmas.point_decompress_lemma (as_seq h0 public);
  let res =
  if b then (
    let rs = sub signature 0ul 32ul in
    let b' = Hacl.Impl.Ed25519.PointDecompress.point_decompress r' rs in
    Spec.Ed25519.Lemmas.point_decompress_lemma (as_seq h0 rs);
    if b' then
      verify_step4 public msg len signature tmp tmp'
    else false
  ) else false in
  res

#pop-options

#set-options "--z3rlimit 40"

inline_for_extraction noextract
val verify:
    public:lbuffer uint8 32ul
  -> len:size_t{v len + 64 <= max_size_t}
  -> msg:lbuffer uint8 len
  -> signature:lbuffer uint8 64ul ->
  Stack bool
    (requires fun h -> live h public /\ live h msg /\ live h signature)
    (ensures  fun h0 z h1 -> modifies0 h0 h1 /\
      z == Spec.Ed25519.verify (as_seq h0 public) (as_seq h0 msg) (as_seq h0 signature)
    )
let verify public msg len signature =
  push_frame();
  let tmp = create 45ul (u64 0) in
  let tmp' = create 32ul (u8 0) in
  let res = verify_step5 public msg len signature tmp tmp' in
  pop_frame();
  res
