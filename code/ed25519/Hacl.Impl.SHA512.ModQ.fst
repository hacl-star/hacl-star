module Hacl.Impl.SHA512.ModQ

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module BSeq = Lib.ByteSequence

module Hash = Hacl.Streaming.SHA2

module BQ = Hacl.Impl.BignumQ
module BD = Hacl.Bignum.Definitions

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val sha512_pre_msg:
    hash:lbuffer uint8 64ul
  -> prefix:lbuffer uint8 32ul
  -> len:size_t
  -> input:lbuffer uint8 len ->
  Stack unit
    (requires fun h ->
      live h hash /\ live h prefix /\ live h input /\
      disjoint input hash /\ disjoint prefix hash)
    (ensures fun h0 _ h1 -> modifies (loc hash) h0 h1 /\
      as_seq h1 hash == Spec.Agile.Hash.hash Spec.Hash.Definitions.SHA2_512
        (Seq.append (as_seq h0 prefix) (as_seq h0 input)))

[@CInline]
let sha512_pre_msg hash prefix len input =
  push_frame ();
  let h0 = ST.get () in
  let st = Hash.alloca_512 () in
  Hash.update_512 st prefix 32ul;
  Hash.update_512 st input len;
  Hash.finish_512 st hash;
  let h1 = ST.get () in
  assert (as_seq h1 hash == Spec.Agile.Hash.hash Spec.Hash.Definitions.SHA2_512
    (Seq.append (Seq.append (Seq.empty) (as_seq h0 prefix)) (as_seq h0 input)));
  Seq.append_empty_l (as_seq h0 prefix);
  pop_frame ()


val sha512_pre_pre2_msg:
    hash:lbuffer uint8 64ul
  -> prefix:lbuffer uint8 32ul
  -> prefix2:lbuffer uint8 32ul
  -> len:size_t
  -> input:lbuffer uint8 len ->
  Stack unit
    (requires fun h ->
      live h hash /\ live h prefix /\ live h prefix2 /\ live h input /\
      disjoint prefix hash /\ disjoint prefix2 hash /\ disjoint input hash)
    (ensures fun h0 _ h1 -> modifies (loc hash) h0 h1 /\
      as_seq h1 hash == Spec.Agile.Hash.hash Spec.Hash.Definitions.SHA2_512
        (Seq.append (Seq.append (as_seq h0 prefix) (as_seq h0 prefix2)) (as_seq h0 input)))

[@CInline]
let sha512_pre_pre2_msg hash prefix prefix2 len input =
  push_frame ();
  let h0 = ST.get () in
  let st = Hash.alloca_512 () in
  Hash.update_512 st prefix 32ul;
  Hash.update_512 st prefix2 32ul;
  Hash.update_512 st input len;
  Hash.finish_512 st hash;
  Seq.append_empty_l (as_seq h0 prefix);
  pop_frame ()


val sha512_modq_pre:
    out:lbuffer uint64 4ul
  -> prefix:lbuffer uint8 32ul
  -> len:size_t
  -> input:lbuffer uint8 len ->
  Stack unit
    (requires fun h ->
      live h input /\ live h out /\ live h prefix /\
      disjoint prefix out /\ disjoint out input)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      BD.bn_v h1 out == Spec.Ed25519.sha512_modq (32 + v len)
        (Seq.append (as_seq h0 prefix) (as_seq h0 input)))

[@CInline]
let sha512_modq_pre out prefix len input =
  push_frame();
  let tmp = create 8ul (u64 0) in
  let hash = create 64ul (u8 0) in
  sha512_pre_msg hash prefix len input;
  let h0 = ST.get () in
  Hacl.Bignum.Convert.mk_bn_from_bytes_le true 64ul hash tmp;
  Hacl.Spec.Bignum.Convert.bn_from_bytes_le_lemma #U64 64 (as_seq h0 hash);
  BQ.modq tmp out;
  pop_frame()


val sha512_modq_pre_pre2:
    out:lbuffer uint64 4ul
  -> prefix:lbuffer uint8 32ul
  -> prefix2:lbuffer uint8 32ul
  -> len:size_t
  -> input:lbuffer uint8 len ->
  Stack unit
    (requires fun h ->
      live h input /\ live h out /\ live h prefix /\ live h prefix2 /\
      disjoint prefix out /\ disjoint prefix2 out /\ disjoint out input)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      BD.bn_v h1 out == Spec.Ed25519.sha512_modq (64 + v len)
        (Seq.append (Seq.append (as_seq h0 prefix) (as_seq h0 prefix2)) (as_seq h0 input)))

[@CInline]
let sha512_modq_pre_pre2 out prefix prefix2 len input =
  push_frame();
  let tmp = create 8ul (u64 0) in
  let hash = create 64ul (u8 0) in
  sha512_pre_pre2_msg hash prefix prefix2 len input;
  let h0 = ST.get () in
  Hacl.Bignum.Convert.mk_bn_from_bytes_le true 64ul hash tmp;
  Hacl.Spec.Bignum.Convert.bn_from_bytes_le_lemma #U64 64 (as_seq h0 hash);
  BQ.modq tmp out;
  pop_frame()


inline_for_extraction noextract
val store_sha512_modq_pre:
    out:lbuffer uint8 32ul
  -> outq:lbuffer uint64 4ul
  -> prefix:lbuffer uint8 32ul
  -> len:size_t
  -> input:lbuffer uint8 len ->
  Stack unit
    (requires fun h ->
      live h input /\ live h out /\ live h prefix /\ live h outq /\
      disjoint prefix out /\ disjoint out input /\ disjoint out outq /\
      disjoint prefix outq /\ disjoint outq input)
    (ensures  fun h0 _ h1 -> modifies (loc out |+| loc outq) h0 h1 /\
      BD.bn_v h1 outq == Spec.Ed25519.sha512_modq (32 + v len) (Seq.append (as_seq h0 prefix) (as_seq h0 input)) /\
      as_seq h1 out == BSeq.nat_to_bytes_le 32 (BD.bn_v h1 outq))

let store_sha512_modq_pre out outq prefix len input =
  sha512_modq_pre outq prefix len input;
  BQ.store_32_bytes out outq


inline_for_extraction noextract
val store_sha512_modq_pre_pre2:
    out:lbuffer uint8 32ul
  -> prefix:lbuffer uint8 32ul
  -> prefix2:lbuffer uint8 32ul
  -> len:size_t
  -> input:lbuffer uint8 len ->
  Stack unit
    (requires fun h ->
      live h input /\ live h out /\ live h prefix /\ live h prefix2 /\
      disjoint prefix out /\ disjoint prefix2 out /\ disjoint out input)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      as_seq h1 out == BSeq.nat_to_bytes_le 32 (Spec.Ed25519.sha512_modq (64 + v len)
        (Seq.append (Seq.append (as_seq h0 prefix) (as_seq h0 prefix2)) (as_seq h0 input))))

let store_sha512_modq_pre_pre2 out prefix prefix2 len input =
  push_frame ();
  let tmp = create 4ul (u64 0) in
  sha512_modq_pre_pre2 tmp prefix prefix2 len input;
  BQ.store_32_bytes out tmp;
  pop_frame ()
