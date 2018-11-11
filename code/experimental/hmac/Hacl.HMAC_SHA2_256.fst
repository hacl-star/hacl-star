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
    output: lbuffer uint8 (Spec.SHA2.size_block a)
  -> key: buffer uint8
  -> len: size_t{v len == length key /\ v len <= Spec.SHA2.max_input a} ->
  Stack unit
  (requires (fun h -> live h output /\ live h key /\ disjoint output key))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let wrap_key output key len = Impl.wrap_key output key len


val init:
    hash: lbuffer uint32 Spec.SHA2.size_hash_w
  -> key: lbuffer uint8 (Spec.SHA2.size_block a) ->
  Stack unit
  (requires (fun h -> live h hash /\ live h key /\ disjoint hash key))
  (ensures  (fun h0 _ h1 -> modifies1 key h0 h1))

let init hash key = Impl.init hash key


val update_block:
    hash: lbuffer uint32 Spec.SHA2.size_hash_w
  -> block: lbuffer uint8 (Spec.SHA2.size_block a) ->
  Stack unit
  (requires (fun h -> live h hash /\ live h block /\ disjoint hash block))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1))

let update_block hash block = Impl.update_block hash block


val update_last:
    hash: lbuffer uint32 Spec.SHA2.size_hash_w
  -> prev: uint64
  -> last: buffer uint8
  -> len: size_t{ v len == length last
               /\ v len <= Spec.SHA2.size_block a
               /\ v len + v prev <= Spec.SHA2.max_input a} ->
  Stack unit
  (requires (fun h -> live h hash /\ live h last /\ disjoint hash last))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1))

let update_last hash prev last len = Impl.update_last hash prev last len


val update:
    hash: lbuffer uint32 Spec.SHA2.size_hash_w
  -> input: buffer uint8
  -> len: size_t{ v len == length input
               /\ v len <= Spec.SHA2.max_input a} ->
  Stack unit
  (requires (fun h -> live h hash /\ live h input /\ disjoint hash input))
  (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1))

let update hash input len = Impl.update hash input len


val finish:
    hash: lbuffer uint8 (Spec.SHA2.size_hash a)
  -> hw: lbuffer uint32 Spec.SHA2.size_hash_w
  -> key: lbuffer uint8 (Spec.SHA2.size_block a) ->
  Stack unit
  (requires (fun h -> live h hash /\ live h key /\ disjoint hash key))
  (ensures  (fun h0 _ h1 -> modifies1 key h0 h1))

let finish hash hw key = Impl.finish hash hw key


val hmac:
    mac: lbuffer uint8 (Spec.SHA2.size_hash a)
  -> key: buffer uint8{length key <= Spec.SHA2.max_input a}
  -> klen: size_t{v klen == length key}
  -> input: buffer uint8{length key + length input + Spec.SHA2.size_block a <= Spec.SHA2.max_input a}
  -> len: size_t{v len == length input} ->
  Stack unit
  (requires (fun h -> live h mac /\ live h key /\ live h input
                 /\ disjoint mac key /\ disjoint mac input))
  (ensures  (fun h0 _ h1 -> modifies1 mac h0 h1))

let hmac mac key klen input len = Impl.hmac mac key klen input len
