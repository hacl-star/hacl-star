module Hacl.Impl.Ed25519.Sign.Steps

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module BSeq = Lib.ByteSequence
module LSeq = Lib.Sequence

module F51 = Hacl.Impl.Ed25519.Field51
module F56 = Hacl.Impl.BignumQ.Mul
module S56 = Hacl.Spec.BignumQ.Definitions

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
let point = lbuffer uint64 20ul

val point_mul_g_compress:
    out:lbuffer uint8 32ul
  -> s:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h ->
      live h out /\ live h s /\ disjoint s out)
    (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      as_seq h1 out == Spec.Ed25519.point_compress (Spec.Ed25519.point_mul_g (as_seq h0 s))
    )

[@CInline]
let point_mul_g_compress out s =
  push_frame();
  let tmp:point = create 20ul (u64 0) in
  Hacl.Impl.Ed25519.Ladder.point_mul_g tmp s;
  Hacl.Impl.Ed25519.PointCompress.point_compress out tmp;
  pop_frame()


inline_for_extraction noextract
val sign_step_2:
    len:size_t{v len + 64 <= max_size_t}
  -> msg:lbuffer uint8 len
  -> tmp_bytes:lbuffer uint8 160ul
  -> tmp_ints:lbuffer uint64 25ul ->
  Stack unit
    (requires fun h ->
      live h msg /\ live h tmp_bytes /\ live h tmp_ints /\
      disjoint tmp_bytes msg /\ disjoint tmp_bytes tmp_ints /\
      disjoint tmp_ints msg)
    (ensures fun h0 _ h1 -> modifies (loc tmp_ints) h0 h1 /\
    (let s = as_seq h1 (gsub tmp_ints 0ul 5ul) in
       v (Seq.index s 0) < pow2 56 /\
       v (Seq.index s 1) < pow2 56 /\
       v (Seq.index s 2) < pow2 56 /\
       v (Seq.index s 3) < pow2 56 /\
       v (Seq.index s 4) < pow2 32) /\
      F56.as_nat h1 (gsub tmp_ints 0ul 5ul) == Spec.Ed25519.sha512_modq (32 + v len)
        (LSeq.concat #uint8 #32 #(v len) (as_seq h0 (gsub tmp_bytes 128ul 32ul)) (as_seq h0 msg)))

let sign_step_2 len msg tmp_bytes tmp_ints =
  let r      = sub tmp_ints 0ul 5ul  in
  let prefix = sub tmp_bytes 128ul 32ul in
  Hacl.Impl.SHA512.ModQ.sha512_modq_pre r prefix len msg


inline_for_extraction noextract
val sign_step_3:
    tmp_bytes:lbuffer uint8 160ul
  -> tmp_ints:lbuffer uint64 25ul ->
  Stack unit
    (requires fun h ->
      live h tmp_bytes /\ live h tmp_ints /\ disjoint tmp_bytes tmp_ints /\
      (let s = as_seq h (gsub tmp_ints 0ul 5ul) in
       v (Seq.index s 0) < pow2 56 /\
       v (Seq.index s 1) < pow2 56 /\
       v (Seq.index s 2) < pow2 56 /\
       v (Seq.index s 3) < pow2 56 /\
       v (Seq.index s 4) < pow2 32)
    )
    (ensures fun h0 _ h1 -> modifies (loc tmp_bytes) h0 h1 /\
      // Framing
      as_seq h0 (gsub tmp_bytes 0ul 32ul) == as_seq h1 (gsub tmp_bytes 0ul 32ul) /\
      as_seq h0 (gsub tmp_bytes 96ul 32ul) == as_seq h1 (gsub tmp_bytes 96ul 32ul) /\
      // Postcondition
      (assert_norm (pow2 56 < pow2 64); assert_norm (pow2 32 < pow2 64);
        assert_norm (S56.as_nat5 (u64 (pow2 56 - 1), u64 (pow2 56 - 1), u64 (pow2 56 - 1), u64 (pow2 56 - 1), u64 (pow2 32 - 1)) < pow2 256);
      as_seq h1 (gsub tmp_bytes 32ul 32ul) ==
      Spec.Ed25519.point_compress (Spec.Ed25519.point_mul_g
        (BSeq.nat_to_bytes_le 32 (F56.as_nat h0 (gsub tmp_ints 0ul 5ul))))))

let sign_step_3 tmp_bytes tmp_ints =
  let a''  = sub tmp_bytes 0ul  32ul in
  let rs' = sub tmp_bytes 32ul 32ul in
  let a    = sub tmp_bytes 96ul 32ul in

  let r  = sub tmp_ints 0ul 5ul  in

  push_frame();
  let rb = create 32ul (u8 0) in
  Hacl.Impl.Store56.store_56 rb r;
  point_mul_g_compress rs' rb;
  pop_frame()


inline_for_extraction noextract
val sign_step_4:
    len:size_t{v len + 64 <= max_size_t}
  -> msg:lbuffer uint8 len
  -> tmp_bytes:lbuffer uint8 160ul
  -> tmp_ints:lbuffer uint64 25ul ->
  Stack unit
    (requires fun h ->
      live h msg /\ live h tmp_bytes /\ live h tmp_ints /\
      disjoint tmp_bytes msg /\ disjoint tmp_bytes tmp_ints /\
      disjoint tmp_ints msg)
    (ensures fun h0 _ h1 -> modifies (loc tmp_ints) h0 h1 /\
      // Framing
      as_seq h0 (gsub tmp_ints 0ul 5ul) == as_seq h1 (gsub tmp_ints 0ul 5ul) /\
      // Postcondition
      F56.qelem_fits h1 (gsub tmp_ints 20ul 5ul) (1, 1, 1, 1, 1) /\
      F56.as_nat h1 (gsub tmp_ints 20ul 5ul) ==
      Spec.Ed25519.sha512_modq (64 + v len)
        (LSeq.concat #uint8 #64 #(v len)
          (LSeq.concat #uint8 #32 #32
            (as_seq h0 (gsub tmp_bytes 32ul 32ul))
            (as_seq h0 (gsub tmp_bytes 0ul 32ul)))
          (as_seq h0 msg)
        )
      )

let sign_step_4 len msg tmp_bytes tmp_ints =
  let r    = sub tmp_ints 0ul 5ul  in
  let h    = sub tmp_ints 20ul 5ul  in

  let a''  = sub tmp_bytes 0ul  32ul in
  let rs'  = sub tmp_bytes 32ul 32ul in
  assert_norm (pow2 56 == 0x100000000000000);
  Hacl.Impl.SHA512.ModQ.sha512_modq_pre_pre2 h rs' a'' len msg


inline_for_extraction noextract
val sign_step_5:
    tmp_bytes:lbuffer uint8 160ul
  -> tmp_ints:lbuffer uint64 25ul ->
  Stack unit
    (requires fun h ->
      live h tmp_bytes /\ live h tmp_ints /\ disjoint tmp_bytes tmp_ints /\
      F56.qelem_fits h (gsub tmp_ints 0ul 5ul) (1, 1, 1, 1, 1) /\
      F56.qelem_fits h (gsub tmp_ints 20ul 5ul) (1, 1, 1, 1, 1) /\
      F56.as_nat h (gsub tmp_ints 0ul 5ul) < Spec.Ed25519.q /\
      F56.as_nat h (gsub tmp_ints 20ul 5ul) < Spec.Ed25519.q
    )
    (ensures fun h0 _ h1 -> modifies (loc tmp_bytes |+| loc tmp_ints) h0 h1 /\
      // Framing
      as_seq h0 (gsub tmp_bytes 32ul 32ul) == as_seq h1 (gsub tmp_bytes 32ul 32ul) /\
      // Postcondition
      (let r = F56.as_nat h0 (gsub tmp_ints 0ul 5ul) in
       let h = F56.as_nat h0 (gsub tmp_ints 20ul 5ul) in
       let a = as_seq h0 (gsub tmp_bytes 96ul 32ul) in
       BSeq.nat_from_bytes_le (as_seq h1 (gsub tmp_bytes 64ul 32ul)) ==
      (r + (h * BSeq.nat_from_bytes_le a) % Spec.Ed25519.q) % Spec.Ed25519.q))

#set-options "--z3rlimit 100"

let sign_step_5 tmp_bytes tmp_ints =
  let r    = sub tmp_ints 0ul 5ul  in
  let aq   = sub tmp_ints 5ul 5ul  in
  let ha   = sub tmp_ints 10ul 5ul  in
  let s    = sub tmp_ints 15ul 5ul  in
  let h    = sub tmp_ints 20ul 5ul  in

  let s'   = sub tmp_bytes 64ul 32ul in
  let rs'  = sub tmp_bytes 32ul 32ul in
  let a    = sub tmp_bytes 96ul 32ul in

  Hacl.Impl.Load56.load_32_bytes aq a;
  Hacl.Impl.BignumQ.Mul.mul_modq ha h aq;
  Hacl.Impl.BignumQ.Mul.add_modq s r ha;
  assert_norm (0x100000000000000 == pow2 56);
  Hacl.Impl.Store56.store_56 s' s
