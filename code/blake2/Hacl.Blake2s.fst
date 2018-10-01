module Hacl.Blake2s

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

module S = Spec.Blake2s
module I = Hacl.Impl.Blake2s


type state = I.state


val mkstate: unit ->
  Stack state
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> True))

let mkstate () = I.blake2s_mkstate ()


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


val update_multi:
    s: state
  -> dd_prev: size_t
  -> dd: size_t{(v dd + v dd_prev) * S.size_block <= max_size_t}
  -> d: lbuffer uint8 (size_v dd * S.size_block) ->
   Stack unit
     (requires (fun h -> True))
     (ensures  (fun h0 _ h1 -> True))

let update_multi s dd_prev dd d = I.blake2s_update_multi s dd_prev dd d


val update_last:
    #vlen: size_t
  -> s: state
  -> ll: size_t
  -> len: size_t
  -> last: lbuffer uint8 (v vlen)
  -> flag_key: bool ->
  Stack unit
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> True))

let update_last #vlen s ll len last fk = I.blake2s_update_last #vlen s ll last len fk


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
    #vll: size_t
  -> #vkk: size_t
  -> #vnn: size_t
  -> output: lbuffer uint8 (v vnn)
  -> outlen:size_t{1 <= v outlen /\ v outlen <= 32}
  -> input: lbuffer uint8 (v vll)
  -> ilen: size_t{v ilen + 2 * S.size_block <= max_size_t /\ ilen == vll}
  -> key: lbuffer uint8 (v vkk)
  -> klen: size_t{v klen <= 32 /\ klen == vkk} ->
  Stack unit
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> True))

let blake2s #vll #vkk #vnn output outlen input ilen key klen = I.blake2s #vll #vkk #vnn output input ilen key klen outlen
