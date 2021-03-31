module Hacl.Impl.Ed25519.Sign.Steps

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module BSeq = Lib.ByteSequence
module LSeq = Lib.Sequence

module F51 = Hacl.Impl.Ed25519.Field51
module BQ = Hacl.Impl.BignumQ

module BD = Hacl.Bignum.Definitions
module BN = Hacl.Bignum
module SD = Hacl.Spec.Bignum.Definitions
module SN = Hacl.Spec.Bignum

#set-options "--z3rlimit 10 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
let point = lbuffer uint64 20ul

val point_mul_g_compress:
    out:lbuffer uint8 32ul
  -> s:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h ->
      live h out /\ live h s /\ disjoint s out)
    (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      as_seq h1 out == Spec.Ed25519.point_compress (Spec.Ed25519.point_mul (as_seq h0 s) Spec.Ed25519.g)
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
  -> tmp_bytes:lbuffer uint8 192ul
  -> tmp_ints:lbuffer uint64 16ul ->
  Stack unit
    (requires fun h ->
      live h msg /\ live h tmp_bytes /\ live h tmp_ints /\
      disjoint tmp_bytes msg /\ disjoint tmp_bytes tmp_ints /\
      disjoint tmp_ints msg)
    (ensures fun h0 _ h1 -> modifies (loc tmp_ints) h0 h1 /\
      BD.bn_v h1 (gsub tmp_ints 0ul 4ul) == Spec.Ed25519.sha512_modq (32 + v len)
        (LSeq.concat #uint8 #32 #(v len) (as_seq h0 (gsub tmp_bytes 160ul 32ul)) (as_seq h0 msg)))

let sign_step_2 len msg tmp_bytes tmp_ints =
  let r      = sub tmp_ints 0ul 4ul  in
  let prefix = sub tmp_bytes 160ul 32ul in
  Hacl.Impl.SHA512.ModQ.sha512_modq_pre r prefix len msg


inline_for_extraction noextract
val sign_step_3:
    tmp_bytes:lbuffer uint8 192ul
  -> tmp_ints:lbuffer uint64 16ul ->
  Stack unit
    (requires fun h ->
      live h tmp_bytes /\ live h tmp_ints /\ disjoint tmp_bytes tmp_ints)
    (ensures fun h0 _ h1 -> modifies (loc tmp_bytes) h0 h1 /\
      // Framing
      as_seq h0 (gsub tmp_bytes 0ul 32ul) == as_seq h1 (gsub tmp_bytes 0ul 32ul) /\
      as_seq h0 (gsub tmp_bytes 128ul 32ul) == as_seq h1 (gsub tmp_bytes 128ul 32ul) /\
      // Postcondition
     (SD.bn_eval_bound (as_seq h0 (gsub tmp_ints 0ul 4ul)) 4;
      as_seq h1 (gsub tmp_bytes 64ul 32ul) ==
      Spec.Ed25519.point_compress (Spec.Ed25519.point_mul
        (BSeq.nat_to_bytes_le 32 (BD.bn_v h0 (gsub tmp_ints 0ul 4ul))) Spec.Ed25519.g)))

let sign_step_3 tmp_bytes tmp_ints =
  let a''  = sub tmp_bytes 0ul  32ul in
  let apre = sub tmp_bytes 128ul 64ul in
  let a    = sub apre 0ul 32ul in
  push_frame();
  let rb = create 32ul (u8 0) in
  let r  = sub tmp_ints 0ul 4ul  in
  let rs' = sub tmp_bytes 64ul 32ul in

  let h0 = ST.get() in
  BN.bn_to_bytes_le 32ul r rb;
  SD.bn_eval_bound (as_seq h0 r) 4;
  SN.bn_to_bytes_le_lemma 32 (as_seq h0 r);
  point_mul_g_compress rs' rb;
  pop_frame()


inline_for_extraction noextract
val sign_step_4:
    len:size_t{v len + 64 <= max_size_t}
  -> msg:lbuffer uint8 len
  -> tmp_bytes:lbuffer uint8 192ul
  -> tmp_ints:lbuffer uint64 16ul ->
  Stack unit
    (requires fun h ->
      live h msg /\ live h tmp_bytes /\ live h tmp_ints /\
      disjoint tmp_bytes msg /\ disjoint tmp_bytes tmp_ints /\
      disjoint tmp_ints msg)
    (ensures fun h0 _ h1 -> modifies (loc tmp_ints) h0 h1 /\
      // Framing
      as_seq h0 (gsub tmp_ints 0ul 4ul) == as_seq h1 (gsub tmp_ints 0ul 4ul) /\
      // Postcondition
      BD.bn_v h1 (gsub tmp_ints 12ul 4ul) ==
      Spec.Ed25519.sha512_modq (64 + v len)
        (LSeq.concat #uint8 #64 #(v len)
          (LSeq.concat #uint8 #32 #32
            (as_seq h0 (gsub tmp_bytes 64ul 32ul))
            (as_seq h0 (gsub tmp_bytes 0ul 32ul)))
          (as_seq h0 msg)
        )
      )

let sign_step_4 len msg tmp_bytes tmp_ints =
  let r    = sub tmp_ints 0ul 4ul  in
  let h    = sub tmp_ints 12ul 4ul  in
  let a''  = sub tmp_bytes 0ul  32ul in
  let rs'  = sub tmp_bytes 64ul 32ul in
  Hacl.Impl.SHA512.ModQ.sha512_modq_pre_pre2 h rs' a'' len msg


inline_for_extraction noextract
val sign_step_5:
    tmp_bytes:lbuffer uint8 192ul
  -> tmp_ints:lbuffer uint64 16ul ->
  Stack unit
    (requires fun h ->
      live h tmp_bytes /\ live h tmp_ints /\ disjoint tmp_bytes tmp_ints /\
      BD.bn_v h (gsub tmp_ints 0ul 4ul) < Spec.Ed25519.q /\
      BD.bn_v h (gsub tmp_ints 12ul 4ul) < Spec.Ed25519.q
    )
    (ensures fun h0 _ h1 -> modifies (loc tmp_bytes |+| loc tmp_ints) h0 h1 /\
      // Framing
      as_seq h0 (gsub tmp_bytes 64ul 32ul) == as_seq h1 (gsub tmp_bytes 64ul 32ul) /\
      // Postcondition
      (let r = BD.bn_v h0 (gsub tmp_ints 0ul 4ul) in
       let h = BD.bn_v h0 (gsub tmp_ints 12ul 4ul) in
       let a = as_seq h0 (gsub tmp_bytes 128ul 32ul) in
      BSeq.nat_from_bytes_le (as_seq h1 (gsub tmp_bytes 96ul 32ul)) ==
      (r + h * BSeq.nat_from_bytes_le a) % Spec.Ed25519.q))

#set-options "--z3rlimit 40"

let sign_step_5 tmp_bytes tmp_ints =
  let r    = sub tmp_ints 0ul 4ul  in
  let aq   = sub tmp_ints 4ul 4ul  in
  let s    = sub tmp_ints 8ul 4ul  in
  let h    = sub tmp_ints 12ul 4ul  in

  let s'   = sub tmp_bytes 96ul 32ul in
  let rs'  = sub tmp_bytes 64ul 32ul in
  let a    = sub tmp_bytes 128ul 32ul in
  let h0 = ST.get () in
  BN.bn_from_bytes_le 32ul a aq;
  SN.bn_from_bytes_le_lemma #U64 32 (as_seq h0 a);
  BQ.mul_add_modq h aq r s;
  let h1 = ST.get () in
  BN.bn_to_bytes_le 32ul s s';
  SN.bn_to_bytes_le_lemma 32 (as_seq h1 s)
