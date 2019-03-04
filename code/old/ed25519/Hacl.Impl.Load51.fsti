module Hacl.Impl.Load51

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.Buffer
open FStar.Old.Endianness

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Endianness
open Hacl.UInt64

open Hacl.Spec.Endianness

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
    /\ (let out = reveal_h64s (as_seq h1 output) in
       let open FStar.UInt64 in
       v (Seq.index out 0) + pow2 51 * v (Seq.index out 1) + pow2 102 * v (Seq.index out 2)  + pow2 153 * v (Seq.index out 3)  + pow2 204 * v (Seq.index out 4) == hlittle_endian (as_seq h0 input) % pow2 255)))
