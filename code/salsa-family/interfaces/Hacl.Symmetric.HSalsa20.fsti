module Hacl.Symmetric.HSalsa20


open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open Hacl.UInt32
open Hacl.Cast


let h32 = Hacl.UInt32.t
let u32 = FStar.UInt32.t
let uint8_p = buffer Hacl.UInt8.t


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 1000"

val crypto_core_hsalsa20:
  output:uint8_p{length output = 32} ->
  input:uint8_p{length input = 16} ->
  key:uint8_p{length key = 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ live h key))
    (ensures  (fun h0 _ h1 -> modifies_1 output h0 h1 /\ live h1 output))
