module Hacl.Blake2s

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

module Spec = Spec.Blake2
module Impl = Hacl.Impl.Blake2s

inline_for_extraction
let op_String_Access #t #n h (b:lbuffer t n) = as_seq h b

let hash_wp = lbuffer uint32 (size 8)
let block_p = lbuffer uint8 (size 64)

val blake2s_init:
    hash: hash_wp
  -> kk: size_t{v kk <= 32}
  -> k: lbuffer uint8 kk
  -> nn: size_t{1 <= v nn /\ v nn <= 32} ->
  Stack unit
    (requires (fun h -> live h hash
                   /\ live h k
                   /\ disjoint hash k
                   /\ disjoint k hash))
    (ensures  (fun h0 _ h1 -> modifies (loc hash) h0 h1
                         /\ h1.[hash] == Spec.Blake2.blake2_init Spec.Blake2S (v kk) h0.[k] (v nn)))

let blake2s_init hash kk k nn = Impl.blake2s_init hash kk k nn


val blake2s_update_block:
    hash:hash_wp
  -> prev:uint64{uint_v prev <= Spec.max_limb Spec.Blake2S}
  -> d:block_p ->
  Stack unit
    (requires (fun h -> live h hash
                   /\ live h d
                   /\ disjoint hash d))
    (ensures  (fun h0 _ h1 -> modifies (loc hash) h0 h1
                         /\ h1.[hash] == Spec.blake2_update_block Spec.Blake2S (uint_v prev) h0.[d] h0.[hash]))

let blake2s_update_block hash prev d = Impl.blake2s_update_block hash prev d


val blake2s_update_last:
    hash: hash_wp
  -> prev: uint64{uint_v prev <= Spec.max_limb Spec.Blake2S}
  -> len: size_t{v len <= Spec.size_block Spec.Blake2S} 
  -> last: lbuffer uint8 len ->
  Stack unit
    (requires (fun h -> live h hash
                   /\ live h last
                   /\ disjoint hash last))
    (ensures  (fun h0 _ h1 -> modifies (loc hash) h0 h1
                         /\ h1.[hash] == Spec.Blake2.blake2_update_last Spec.Blake2S (uint_v prev) (v len) h0.[last] h0.[hash]))

let blake2s_update_last hash prev len last = Impl.blake2s_update_last hash prev len last


val blake2s_finish:
    nn: size_t{1 <= v nn /\ v nn <= 32} 
  -> output: lbuffer uint8 nn
  -> hash: hash_wp ->
  Stack unit
    (requires (fun h -> live h hash
                   /\ live h output
                   /\ disjoint output hash
                   /\ disjoint hash output))
    (ensures  (fun h0 _ h1 -> modifies (loc output) h0 h1
                         /\ h1.[output] == Spec.Blake2.blake2_finish Spec.Blake2S h0.[hash] (v nn)))

let blake2s_finish output hash nn = Impl.blake2s_finish output hash nn


val blake2s:
    nn:size_t{1 <= v nn /\ v nn <= 32} 
  -> output: lbuffer uint8 nn
  -> ll: size_t
  -> d: lbuffer uint8 ll
  -> kk: size_t{v kk <= 32 /\ (if v kk = 0 then v ll < pow2 64 else v ll + 64 < pow2 64)}
  -> k: lbuffer uint8 kk ->
  Stack unit
    (requires (fun h -> live h output
                   /\ live h d
                   /\ live h k
                   /\ disjoint output d
                   /\ disjoint output k))
    (ensures  (fun h0 _ h1 -> modifies (loc output) h0 h1
                         /\ h1.[output] == Spec.Blake2.blake2s h0.[d] (v kk) h0.[k] (v nn)))

let blake2s nn output ll d kk k = Impl.blake2s nn output ll d kk k
