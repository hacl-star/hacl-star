module Hacl.Blake2s

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

module S = Spec.Blake2s
module I = Hacl.Impl.Blake2s


type state = I.state


val mkstate: unit ->
  Stack state
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> True))

let mkstate () = I.blake2s_mkstate ()


val init:
    #vkk:size_nat
  -> st:state
  -> k:lbuffer uint8 vkk
  -> kk:size_t{v kk <= 32 /\ v kk = vkk}
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
    #vlen: size_nat
  -> s: state
  -> ll: size_t
  -> len: size_t
  -> last: lbuffer uint8 vlen
  -> flag_key: bool ->
  Stack unit
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> True))

let update_last #vlen s ll len last fk = I.blake2s_update_last #vlen s ll len last fk


val finish:
    #vnn: size_nat
  -> output: lbuffer uint8 vnn
  -> st: state
  -> nn: size_t{v nn = vnn} ->
  Stack unit
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> True))

let finish #vnn output st nn = I.blake2s_finish #vnn output st nn


(*
val blake2s:
    #vll: size_nat
  -> #vkk: size_nat
  -> #vnn: size_nat
  -> output: lbuffer uint8 vnn
  -> outlen:size_t{1 <= v outlen /\ v outlen <= 32 /\ v outlen = v outlen}
  -> input: lbuffer uint8 vll
  -> ilen: size_t{v ilen + 2 * S.size_block <= max_size_t /\ v ilen = vll}
  -> key: lbuffer uint8 vkk
  -> klen: size_t{v klen <= 32 /\ v klen = vkk} ->
  Stack unit
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> True))

let blake2s #vll #vkk #vnn output outlen input ilen key klen = I.blake2s #vll #vkk #vnn output input ilen klen key outlen
*)
