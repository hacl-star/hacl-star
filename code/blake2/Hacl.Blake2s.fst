module Hacl.Blake2s

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

module S = Spec.Blake2s
module I = Hacl.Impl.Blake2s


type state = I.state

val init:
    #vkk:size_t
  -> st:state
  -> k:lbuffer uint8 (v vkk)
  -> kk:size_t{v kk <= 32 /\ kk == vkk}
  -> nn:size_t{1 <= v nn /\ v nn <= 32} ->
  Stack unit
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> True))

let init #vkk st k kk nn = I.blake2s_init #vkk st k kk nn


val update_block:
    s:state
  -> n:size_t
  -> d:lbuffer uint8 S.size_block ->
  Stack unit
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> True))

let update_block s n block = I.blake2s_update_block s n block


val update_last:
    #vlen: size_t
  -> s: state
  -> ll: size_t
  -> len: size_t
  -> last: lbuffer uint8 (v vlen) ->
  Stack unit
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> True))

let update_last #vlen s ll len last = I.blake2s_update_last #vlen s ll last len


val finish:
    #vnn: size_t
  -> output: lbuffer uint8 (v vnn)
  -> st: state
  -> nn: size_t{nn == vnn} ->
  Stack unit
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> True))

let finish #vnn output st nn = I.blake2s_finish #vnn output st nn


val blake2s:
    output: buffer uint8
  -> d: buffer uint8
  -> ll: size_t{length d == v ll}
  -> k: buffer uint8
  -> kk: size_t{length k == v kk /\ v kk <= 32 /\ (if v kk = 0 then v ll < pow2 64 else v ll + 64 < pow2 64)}
  -> nn:size_t{1 <= v nn /\ v nn <= 32} ->
  Stack unit
    (requires (fun h -> LowStar.Buffer.live h output
                   /\ LowStar.Buffer.live h d
                   /\ LowStar.Buffer.live h k
                   /\ LowStar.Buffer.disjoint output d
                   /\ LowStar.Buffer.disjoint output k))
    (ensures  (fun h0 _ h1 -> LowStar.Buffer.modifies (LowStar.Buffer.loc_buffer output) h0 h1
                         /\ h1.[output] == Spec.Blake2.blake2s h0.[d] (v kk) h0.[k] (v nn)))

let blake2s output d ll k kk nn = I.blake2s output d ll k kk nn
