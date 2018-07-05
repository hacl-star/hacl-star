module Hacl.Keccak

open FStar.HyperStack.All
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Buffer
open Lib.ByteBuffer
open FStar.Mul

let lbytes len = lbuffer uint8 len
let v = size_v

val cshake128_frodo:
  input_len:size_t -> input:lbytes (v input_len) -> cstm:uint16 ->
  output_len:size_t -> output:lbytes (v output_len) -> Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))


val cshake256_frodo:
  input_len:size_t -> input:lbytes (v input_len) -> cstm:uint16 ->
  output_len:size_t -> output:lbytes (v output_len) -> Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))
