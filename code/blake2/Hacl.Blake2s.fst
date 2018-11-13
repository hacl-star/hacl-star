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
    #vkk:size_t
  -> hash:hash_wp
  -> k:lbuffer uint8 (v vkk)
  -> kk:size_t{v kk <= 32 /\ kk == vkk}
  -> nn:size_t{1 <= v nn /\ v nn <= 32} ->
  Stack unit
    (requires (fun h -> LowStar.Buffer.live h hash
                   /\ LowStar.Buffer.live h k
                   /\ LowStar.Buffer.disjoint hash k
                   /\ LowStar.Buffer.disjoint k hash))
    (ensures  (fun h0 _ h1 -> LowStar.Buffer.modifies (LowStar.Buffer.loc_buffer hash) h0 h1
                         /\ h1.[hash] == Spec.Blake2.blake2_init Spec.Blake2S (v kk) h0.[k] (v nn)))

let blake2s_init #vkk hash k kk nn = Impl.blake2s_init #vkk hash k kk nn


val blake2s_update_block:
    hash:hash_wp
  -> prev:uint64{uint_v prev <= Spec.max_limb Spec.Blake2S}
  -> d:block_p ->
  Stack unit
    (requires (fun h -> LowStar.Buffer.live h hash
                   /\ LowStar.Buffer.live h d
                   /\ LowStar.Buffer.disjoint hash d))
    (ensures  (fun h0 _ h1 -> LowStar.Buffer.modifies (LowStar.Buffer.loc_buffer hash) h0 h1
                         /\ h1.[hash] == Spec.blake2_update_block Spec.Blake2S (uint_v prev) h0.[d] h0.[hash]))

let blake2s_update_block hash prev d = Impl.blake2s_update_block hash prev d


val blake2s_update_last:
    #vlen: size_t
  -> hash: hash_wp
  -> prev: uint64{uint_v prev <= Spec.max_limb Spec.Blake2S}
  -> last: lbuffer uint8 (v vlen)
  -> len: size_t{v len <= Spec.size_block Spec.Blake2S /\ len == vlen} ->
  Stack unit
    (requires (fun h -> LowStar.Buffer.live h hash
                   /\ LowStar.Buffer.live h last
                   /\ LowStar.Buffer.disjoint hash last))
    (ensures  (fun h0 _ h1 -> LowStar.Buffer.modifies (LowStar.Buffer.loc_buffer hash) h0 h1
                         /\ h1.[hash] == Spec.Blake2.blake2_update_last Spec.Blake2S (uint_v prev) (v len) h0.[last] h0.[hash]))

let blake2s_update_last #vlen hash prev last len = Impl.blake2s_update_last #vlen hash prev last len


val blake2s_finish:
    #vnn: size_t
  -> output: lbuffer uint8 (v vnn)
  -> hash: hash_wp
  -> nn: size_t{1 <= v nn /\ v nn <= 32 /\ nn == vnn} ->
  Stack unit
    (requires (fun h -> LowStar.Buffer.live h hash
                   /\ LowStar.Buffer.live h output
                   /\ LowStar.Buffer.disjoint output hash
                   /\ LowStar.Buffer.disjoint hash output))
    (ensures  (fun h0 _ h1 -> LowStar.Buffer.modifies (LowStar.Buffer.loc_buffer output) h0 h1
                         /\ h1.[output] == Spec.Blake2.blake2_finish Spec.Blake2S h0.[hash] (v nn)))

let blake2s_finish #vnn output hash nn = Impl.blake2s_finish #vnn output hash nn


val blake2s:
    output: buffer uint8
  -> d: buffer uint8
  -> ll: size_t{length d == v ll}
  -> k: buffer uint8
  -> kk: size_t{length k == v kk /\ v kk <= 32 /\ (if v kk = 0 then v ll < pow2 64 else v ll + 64 < pow2 64)}
  -> nn:size_t{v nn == length output /\ 1 <= v nn /\ v nn <= 32} ->
  Stack unit
    (requires (fun h -> LowStar.Buffer.live h output
                   /\ LowStar.Buffer.live h d
                   /\ LowStar.Buffer.live h k
                   /\ LowStar.Buffer.disjoint output d
                   /\ LowStar.Buffer.disjoint output k))
    (ensures  (fun h0 _ h1 -> LowStar.Buffer.modifies (LowStar.Buffer.loc_buffer output) h0 h1
                         /\ h1.[output] == Spec.Blake2.blake2s h0.[d] (v kk) h0.[k] (v nn)))

let blake2s output d ll k kk nn = Impl.blake2s output d ll k kk nn
