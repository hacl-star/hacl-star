module Hacl.Keccak

open FStar.HyperStack.All
open Lib.IntTypes
open Lib.PQ.Buffer
open Hacl.Impl.PQ.Lib

open LowStar.ModifiesPat
open LowStar.Modifies

module Buf = LowStar.Buffer

val cshake128_frodo:
  input_len:size_t -> input:lbytes input_len -> cstm:uint16 ->
  output_len:size_t -> output:lbytes output_len -> Stack unit
  (requires (fun h -> Buf.live h input /\ Buf.live h output /\ Buf.disjoint input output))
  (ensures (fun h0 _ h1 -> Buf.live h1 output /\ modifies (loc_buffer output) h0 h1))

val cshake256_frodo:
  input_len:size_t -> input:lbytes input_len -> cstm:uint16 ->
  output_len:size_t -> output:lbytes output_len -> Stack unit
  (requires (fun h -> Buf.live h input /\ Buf.live h output /\ Buf.disjoint input output))
  (ensures (fun h0 _ h1 -> Buf.live h1 output /\ modifies (loc_buffer output) h0 h1))
