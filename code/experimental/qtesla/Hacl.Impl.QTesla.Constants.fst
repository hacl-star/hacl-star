module Hacl.Impl.QTesla.Constants

open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Hacl.SHA3
module S = Spec.SHA3

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

unfold let shake128_rate = size 168
unfold let shake256_rate = size 136

// Implementation of cSHAKE gets inlined for extraction. To make things easier to compare to the
// reference code, we enclose it in our own wrapper so it appears as a function call in callers.
(*val cshake128_qtesla:
    input_len:size_t
  -> input:lbuffer uint8 input_len
  -> cstm:uint16
  -> output_len:size_t
  -> output:lbuffer uint8 output_len
  -> Stack unit
    (requires fun h -> live h input /\ live h output /\ disjoint input output)
    (ensures  fun h0 _ h1 ->
      modifies (loc output) h0 h1 /\
      as_seq h1 output ==
      S.cshake128_frodo (v input_len) (as_seq h0 input) cstm (v output_len))

let cshake128_qtesla input_len input cstm output_len output = cshake128_frodo input_len input cstm output_len output

val cshake256_qtesla:
    input_len:size_t
  -> input:lbuffer uint8 input_len
  -> cstm:uint16
  -> output_len:size_t
  -> output:lbuffer uint8 output_len
  -> Stack unit
    (requires fun h -> live h input /\ live h output /\ disjoint input output)
    (ensures  fun h0 _ h1 ->
      modifies (loc output) h0 h1 /\
      as_seq h1 output ==
      S.cshake256_frodo (v input_len) (as_seq h0 input) cstm (v output_len))

let cshake256_qtesla input_len input cstm output_len output = cshake256_frodo input_len input cstm output_len output*)
let cshake128_qtesla = cshake128_frodo
let cshake256_qtesla = cshake256_frodo
