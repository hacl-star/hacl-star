module Hacl.Impl.SHA512.ModQ

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

#reset-options "--max_fuel 0 --max_ifuel 0"

open Spec.Hash.Definitions

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
    (ensures fun h0 _ h1 -> modifies (loc hash) h0 h1)
let sha512_pre_msg h prefix len input =
  push_frame ();
  let pre_msg = create (len +. 32ul) (u8 0) in
  concat2 32ul prefix len input pre_msg;  
  assume(length pre_msg < max_input_length SHA2_512);
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
      disjoint prefix hash /\ disjoint prefix2 hash /\ disjoint input hash)
    (ensures fun h0 _ h1 -> modifies (loc hash) h0 h1)
let sha512_pre_pre2_msg h prefix prefix2 len input =
  push_frame ();
  let pre_msg = create (len +. 64ul) (u8 0) in
  concat3 32ul prefix 32ul prefix2 len input pre_msg;
  assume(length pre_msg < max_input_length SHA2_512);
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
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1)
let sha512_modq_pre out prefix len input =
  push_frame();
  let tmp = create 10ul (u64 0) in
  let hash = create 64ul (u8 0) in
  sha512_pre_msg hash prefix len input;
  Hacl.Impl.Load56.load_64_bytes tmp hash;
  Hacl.Impl.BignumQ.Mul.barrett_reduction out tmp;
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
    (ensures  fun h0 _ h1 ->  modifies (loc out) h0 h1)
let sha512_modq_pre_pre2 out prefix prefix2 len input =
  push_frame();
  let tmp = create 10ul (u64 0) in
  let hash = create 64ul (u8 0) in
  sha512_pre_pre2_msg hash prefix prefix2 len input;
  Hacl.Impl.Load56.load_64_bytes tmp hash;
  Hacl.Impl.BignumQ.Mul.barrett_reduction out tmp;
  pop_frame()
