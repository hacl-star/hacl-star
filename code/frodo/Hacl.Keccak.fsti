module Hacl.Keccak

open FStar.HyperStack.All
open Lib.IntTypes
open Lib.PQ.Buffer
open Hacl.Impl.PQ.Lib

val cshake128_frodo:
  input_len:size_t -> input:lbytes input_len -> cstm:uint16 ->
  output_len:size_t -> output:lbytes output_len -> Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))


val cshake256_frodo:
  input_len:size_t -> input:lbytes input_len -> cstm:uint16 ->
  output_len:size_t -> output:lbytes output_len -> Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))
