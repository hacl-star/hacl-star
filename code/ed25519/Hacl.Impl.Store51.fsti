module Hacl.Impl.Store51

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Buffer
open FStar.Endianness
open FStar.Mul

open Hacl.UInt64
open Hacl.Spec.Endianness
open Hacl.Endianness


#reset-options "--max_fuel 0 --z3rlimit 100"

[@ Substitute]
val store_51:
  output:buffer Hacl.UInt8.t{Buffer.length output = 32} ->
  input:buffer Hacl.UInt64.t{Buffer.length input = 5} ->
  Stack unit
    (requires (fun h -> Buffer.live h input /\
      Hacl.Bignum25519.red_51 (as_seq h input) /\
      (let s = as_seq h input in v (Seq.index s 0) + pow2 51 * v (Seq.index s 1)
                               + pow2 102 * v (Seq.index s 2) + pow2 153 * v (Seq.index s 3)
                               + pow2 204 * v (Seq.index s 4) < pow2 255 - 19) /\
      Buffer.live h output))
    (ensures (fun h0 _ h1 -> Buffer.live h0 input /\ Buffer.live h1 input /\
      modifies_1 output h0 h1 /\
      Buffer.live h1 output /\
      hlittle_endian (as_seq h1 output) == Hacl.Bignum25519.seval (as_seq h0 input)))
