module Hacl.Impl.SHA512.ModQ

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module BQ = Hacl.Impl.BignumQ
module BD = Hacl.Bignum.Definitions
module BN = Hacl.Bignum
module SN = Hacl.Spec.Bignum

#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

//FIX
val sha512_pre_msg:
    hash:lbuffer uint8 64ul
  -> prefix:lbuffer uint8 32ul
  -> len:size_t{v len + 32 <= max_size_t}
  -> input:lbuffer uint8 len ->
  Stack unit
    (requires fun h ->
      live h hash /\ live h prefix /\ live h input /\
      disjoint input hash /\ disjoint prefix hash)
    (ensures fun h0 _ h1 -> modifies (loc hash) h0 h1 /\
      as_seq h1 hash == Spec.Agile.Hash.hash Spec.Hash.Definitions.SHA2_512
           (LSeq.concat #uint8 #32 #(v len) (as_seq h0 prefix) (as_seq h0 input))
    )

[@CInline]
let sha512_pre_msg h prefix len input =
  push_frame ();
  assert_norm(pow2 32 <= pow2 125 - 1);
  let pre_msg = create (len +. 32ul) (u8 0) in
  concat2 32ul prefix len input pre_msg;
  Hacl.Hash.SHA2.hash_512_lib (len +. 32ul) pre_msg h;
  pop_frame ()


//FIX
val sha512_pre_pre2_msg:
    hash:lbuffer uint8 64ul
  -> prefix:lbuffer uint8 32ul
  -> prefix2:lbuffer uint8 32ul
  -> len:size_t{v len + 64 <= max_size_t}
  -> input:lbuffer uint8 len ->
  Stack unit
    (requires fun h ->
      live h hash /\ live h prefix /\ live h prefix2 /\ live h input /\
      disjoint prefix hash /\ disjoint prefix2 hash /\ disjoint input hash
    )
    (ensures fun h0 _ h1 -> modifies (loc hash) h0 h1 /\
      as_seq h1 hash == Spec.Agile.Hash.hash Spec.Hash.Definitions.SHA2_512
        (LSeq.concat #uint8 #64 #(v len)
          (LSeq.concat #uint8 #32 #32 (as_seq h0 prefix) (as_seq h0 prefix2))
          (as_seq h0 input)
        )
    )

[@CInline]
let sha512_pre_pre2_msg h prefix prefix2 len input =
  push_frame ();
  let pre_msg = create (len +. 64ul) (u8 0) in
  assert_norm(pow2 32 <= pow2 125 - 1);
  concat3 32ul prefix 32ul prefix2 len input pre_msg;
  Hacl.Hash.SHA2.hash_512_lib (len +. 64ul) pre_msg h;
  pop_frame ()


val sha512_modq_pre:
    out:lbuffer uint64 4ul
  -> prefix:lbuffer uint8 32ul
  -> len:size_t{v len + 32 <= max_size_t}
  -> input:lbuffer uint8 len ->
  Stack unit
    (requires fun h ->
      live h input /\ live h out /\ live h prefix /\
      disjoint prefix out /\  disjoint out input)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      BD.bn_v h1 out ==
      Spec.Ed25519.sha512_modq (32 + v len)
        (LSeq.concat #uint8 #32 #(v len) (as_seq h0 prefix) (as_seq h0 input)))

[@CInline]
let sha512_modq_pre out prefix len input =
  push_frame();
  let tmp = create 8ul (u64 0) in
  let hash = create 64ul (u8 0) in
  sha512_pre_msg hash prefix len input;
  let h0 = ST.get () in
  BN.bn_from_bytes_le 64ul hash tmp;
  SN.bn_from_bytes_le_lemma #U64 64 (as_seq h0 hash);
  BQ.modq tmp out;
  pop_frame()


val sha512_modq_pre_pre2:
    out:lbuffer uint64 4ul
  -> prefix:lbuffer uint8 32ul
  -> prefix2:lbuffer uint8 32ul
  -> len:size_t{v len + 64 <= max_size_t}
  -> input:lbuffer uint8 len ->
  Stack unit
    (requires fun h ->
      live h input /\ live h out /\ live h prefix /\ live h prefix2 /\
      disjoint prefix out /\ disjoint prefix2 out /\ disjoint out input)
    (ensures  fun h0 _ h1 ->  modifies (loc out) h0 h1 /\
      BD.bn_v h1 out ==
      Spec.Ed25519.sha512_modq (64 + v len)
        (LSeq.concat #uint8 #64 #(v len)
          (LSeq.concat #uint8 #32 #32
            (as_seq h0 prefix)
            (as_seq h0 prefix2))
          (as_seq h0 input)
        )
      )

[@CInline]
let sha512_modq_pre_pre2 out prefix prefix2 len input =
  push_frame();
  let tmp = create 8ul (u64 0) in
  let hash = create 64ul (u8 0) in
  sha512_pre_pre2_msg hash prefix prefix2 len input;
  let h0 = ST.get () in
  BN.bn_from_bytes_le 64ul hash tmp;
  SN.bn_from_bytes_le_lemma #U64 64 (as_seq h0 hash);
  BQ.modq tmp out;
  pop_frame()
