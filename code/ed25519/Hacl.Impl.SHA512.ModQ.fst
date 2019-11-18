module Hacl.Impl.SHA512.ModQ

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.ByteSequence
open Lib.Sequence
open Lib.Buffer

module F56 = Hacl.Impl.Ed25519.Field56

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
           (concat #uint8 #32 #(v len) (as_seq h0 prefix) (as_seq h0 input))
    )
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
        (concat #uint8 #64 #(v len)
          (concat #uint8 #32 #32 (as_seq h0 prefix) (as_seq h0 prefix2))
          (as_seq h0 input)
        )
    )


let sha512_pre_pre2_msg h prefix prefix2 len input =
  push_frame ();
  let pre_msg = create (len +. 64ul) (u8 0) in
  assert_norm(pow2 32 <= pow2 125 - 1);
  concat3 32ul prefix 32ul prefix2 len input pre_msg;
  Hacl.Hash.SHA2.hash_512_lib (len +. 64ul) pre_msg h;
  pop_frame ()

val sha512_modq_pre:
    out:lbuffer uint64 5ul
  -> prefix:lbuffer uint8 32ul
  -> len:size_t{v len + 32 <= max_size_t}
  -> input:lbuffer uint8 len ->
  Stack unit
    (requires fun h ->
      live h input /\ live h out /\ live h prefix /\
      disjoint prefix out /\  disjoint out input)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      (let s = as_seq h1 out in
       v (Seq.index s 0) < pow2 56 /\
       v (Seq.index s 1) < pow2 56 /\
       v (Seq.index s 2) < pow2 56 /\
       v (Seq.index s 3) < pow2 56 /\
       v (Seq.index s 4) < pow2 32) /\
      F56.as_nat h1 out ==
      Spec.Ed25519.sha512_modq (32 + v len)
        (concat #uint8 #32 #(v len) (as_seq h0 prefix) (as_seq h0 input))
    )

let sha512_modq_pre out prefix len input =
  push_frame();
  let tmp = create 10ul (u64 0) in
  let hash = create 64ul (u8 0) in
  sha512_pre_msg hash prefix len input;
  Hacl.Impl.Load56.load_64_bytes tmp hash;
  Hacl.Impl.BignumQ.Mul.barrett_reduction out tmp;
  assert_norm (pow2 56 == 0x100000000000000);
  pop_frame()

val sha512_modq_pre_pre2:
    out:lbuffer uint64 5ul
  -> prefix:lbuffer uint8 32ul
  -> prefix2:lbuffer uint8 32ul
  -> len:size_t{v len + 64 <= max_size_t}
  -> input:lbuffer uint8 len ->
  Stack unit
    (requires fun h ->
      live h input /\ live h out /\ live h prefix /\ live h prefix2 /\
      disjoint prefix out /\ disjoint prefix2 out /\ disjoint out input)
    (ensures  fun h0 _ h1 ->  modifies (loc out) h0 h1 /\
      (let s = as_seq h1 out in
       v (Seq.index s 0) < pow2 56 /\
       v (Seq.index s 1) < pow2 56 /\
       v (Seq.index s 2) < pow2 56 /\
       v (Seq.index s 3) < pow2 56 /\
       v (Seq.index s 4) < pow2 32) /\
     F56.as_nat h1 out ==
      Spec.Ed25519.sha512_modq (64 + v len)
        (concat #uint8 #64 #(v len)
          (concat #uint8 #32 #32
            (as_seq h0 prefix)
            (as_seq h0 prefix2))
          (as_seq h0 input)
        )
      )
let sha512_modq_pre_pre2 out prefix prefix2 len input =
  push_frame();
  let tmp = create 10ul (u64 0) in
  let hash = create 64ul (u8 0) in
  sha512_pre_pre2_msg hash prefix prefix2 len input;
  Hacl.Impl.Load56.load_64_bytes tmp hash;
  Hacl.Impl.BignumQ.Mul.barrett_reduction out tmp;
  assert_norm (pow2 56 == 0x100000000000000);
  pop_frame()
