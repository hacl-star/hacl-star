module Hacl.Blake2s

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

module Spec = Spec.Blake2
module Impl = Hacl.Impl.Blake2s


let hash_wp = lbuffer uint32 8
let block_p = lbuffer uint8 64


val blake2s_init:
    hash: hash_wp
  -> k: buffer uint8
  -> kk: size_t{v kk <= 32 /\ kk == length k}
  -> nn: size_t{1 <= v nn /\ v nn <= 32} ->
  Stack unit
    (requires (fun h -> live h hash
                   /\ live h k
                   /\ disjoint hash k
                   /\ disjoint k hash))
    (ensures  (fun h0 _ h1 -> modifies (loc hash) h0 h1
                         /\ h1.[hash] == Spec.Blake2.blake2_init Spec.Blake2S (v kk) (as_seq #MUT #uint8 #kk h0 k) (v nn)))

let blake2s_init hash k kk nn = Impl.blake2s_init hash k kk nn


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
  -> last: buffer uint8
  -> len: size_t{v len <= Spec.size_block Spec.Blake2S /\ v len == length last} ->
  Stack unit
    (requires (fun h -> live h hash
                   /\ live h last
                   /\ disjoint hash last))
    (ensures  (fun h0 _ h1 -> modifies (loc hash) h0 h1
                         /\ h1.[hash] == Spec.Blake2.blake2_update_last Spec.Blake2S (uint_v prev) (v len) (as_seq #MUT #uint8 #len h0 last) h0.[hash]))

let blake2s_update_last hash prev last len = Impl.blake2s_update_last hash prev last len


val blake2s_finish:
    output: buffer uint8
  -> hash: hash_wp
  -> nn: size_t{1 <= v nn /\ v nn <= 32 /\ v nn == length output} ->
  Stack unit
    (requires (fun h -> live h hash
                   /\ live h output
                   /\ disjoint output hash
                   /\ disjoint hash output))
    (ensures  (fun h0 _ h1 -> modifies (loc output) h0 h1
                         /\ (as_seq #MUT #uint8 #nn h1 output) == Spec.Blake2.blake2_finish Spec.Blake2S h0.[hash] (v nn)))

let blake2s_finish output hash nn = Impl.blake2s_finish output hash nn


val blake2s:
    output: buffer uint8
  -> d: buffer uint8
  -> ll: size_t{length d == v ll}
  -> k: buffer uint8
  -> kk: size_t{length k == v kk /\ v kk <= 32 /\ (if v kk = 0 then v ll < pow2 64 else v ll + 64 < pow2 64)}
  -> nn:size_t{v nn == length output /\ 1 <= v nn /\ v nn <= 32} ->
  Stack unit
    (requires (fun h -> live h output
                   /\ live h d
                   /\ live h k
                   /\ disjoint output d
                   /\ disjoint output k))
    (ensures  (fun h0 _ h1 -> modifies (loc output) h0 h1
                         /\ (as_seq #MUT #uint8 #nn h1 output) == Spec.Blake2.blake2s (as_seq #MUT #uint8 #ll h0 d) (v kk) (as_seq #MUT #uint8 #kk h0 k) (v nn)))

let blake2s output d ll k kk nn = Impl.blake2s output d ll k kk nn
