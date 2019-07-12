module Hacl.HMAC_SHA2_256

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.LoopCombinators

module ST = FStar.HyperStack.ST
module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators


module Impl = Hacl.Impl.HMAC_SHA2_256


inline_for_extraction noextract
let a = Spec.SHA2.SHA2_256


(* Key wrapping function *)
val wrap_key:
    output: lbuffer uint8 (size (Spec.SHA2.size_block a))
  -> key: buffer uint8
  -> len: size_t{v len == length key /\ v len <= Spec.SHA2.max_input a} ->
  Stack unit
  (requires (fun h -> live h output /\ live h key /\ disjoint output key))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let wrap_key output key len = Impl.wrap_key output key len


val init:
    state: lbuffer uint32 (size Spec.SHA2.size_hash_w)
  -> key: lbuffer uint8 (size (Spec.SHA2.size_block a)) ->
  Stack unit
  (requires (fun h -> live h state /\ live h key /\ disjoint state key))
  (ensures  (fun h0 _ h1 -> modifies1 state h0 h1))

let init state key = Impl.init state key


val update_block:
    state: lbuffer uint32 (size Spec.SHA2.size_hash_w)
  -> block: lbuffer uint8 (size (Spec.SHA2.size_block a)) ->
  Stack unit
  (requires (fun h -> live h state /\ live h block /\ disjoint state block))
  (ensures  (fun h0 _ h1 -> modifies1 state h0 h1))

let update_block state block = Impl.update_block state block


val update_last:
    state: lbuffer uint32 (size Spec.SHA2.size_hash_w)
  -> prev: uint64
  -> last: buffer uint8
  -> len: size_t{ v len == length last
               /\ v len <= Spec.SHA2.size_block a
               /\ v len + uint_v prev <= Spec.SHA2.max_input a} ->
  Stack unit
  (requires (fun h -> live h state /\ live h last /\ disjoint state last))
  (ensures  (fun h0 _ h1 -> modifies1 state h0 h1))

let update_last state prev last len = Impl.update_last state prev last len


val update:
    state: lbuffer uint32 (size Spec.SHA2.size_hash_w)
  -> input: buffer uint8
  -> len: size_t{ v len == length input
               /\ v len <= Spec.SHA2.max_input a} ->
  Stack unit
  (requires (fun h -> live h state /\ live h input /\ disjoint state input))
  (ensures  (fun h0 _ h1 -> modifies1 state h0 h1))

let update state input len = Impl.update state input len


val finish:
    hash: lbuffer uint8 (size (Spec.SHA2.size_hash a))
  -> state: lbuffer uint32 (size Spec.SHA2.size_hash_w)
  -> key: lbuffer uint8 (size (Spec.SHA2.size_block a)) ->
  Stack unit
  (requires (fun h -> live h hash /\ live h state /\ live h key
                 /\ disjoint hash key /\ disjoint hash state))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1))

let finish hash state key = Impl.finish hash state key


val hmac:
    mac: lbuffer uint8 (size (Spec.SHA2.size_hash a))
  -> key: buffer uint8{length key <= Spec.SHA2.max_input a}
  -> klen: size_t{v klen == length key}
  -> input: buffer uint8{length key + length input + Spec.SHA2.size_block a <= Spec.SHA2.max_input a}
  -> len: size_t{v len == length input} ->
  Stack unit
  (requires (fun h -> live h mac /\ live h key /\ live h input
                 /\ disjoint mac key /\ disjoint mac input))
  (ensures  (fun h0 _ h1 -> modifies1 mac h0 h1))

let hmac mac key klen input len = Impl.hmac mac key klen input len
