module Hacl.Impl.Load51

open FStar.Mul
open FStar.Buffer
open FStar.Endianness

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Endianness
open Hacl.UInt64


#reset-options "--max_fuel 0 --z3rlimit 10"

let u32 = UInt32.t
let h8 = Hacl.UInt8.t
let h64 = Hacl.UInt64.t
let hint8_p = buffer h8

val load_51: output:felem -> input:hint8_p{length input = 32} -> Stack unit
  (requires (fun h -> Buffer.live h output /\ Buffer.live h input))
  (ensures (fun h0 _ h1 -> Buffer.live h0 output /\ Buffer.live h0 input
    /\ Buffer.live h1 output /\ modifies_1 output h0 h1
    /\ Hacl.Bignum25519.red_51 (as_seq h1 output)
    /\ (let out = as_seq h1 output in
       v (Seq.index out 0) + pow2 51 * v (Seq.index out 1) + pow2 102 * v (Seq.index out 2)  + pow2 153 * v (Seq.index out 3)  + pow2 204 * v (Seq.index out 4) == Endianness.little_endian (as_seq h0 input) % pow2 255)))
