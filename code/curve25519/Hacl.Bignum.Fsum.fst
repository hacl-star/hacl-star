module Hacl.Bignum.Fsum

open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Spec.Bignum.Fsum

module U32 = FStar.UInt32

#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

let red_c h (f:felem) ctr = live h f /\ red (as_seq h f) ctr

[@"substitute"]
inline_for_extraction val fsum_:
  a:felem ->
  b:felem{disjoint a b} ->
  i:ctr{U32.v i <= len} ->
  Stack unit
    (requires (fun h -> red_c h a (U32.v i) /\ red_c h b (U32.v i) /\ len = 5))
    (ensures (fun h0 _ h1 -> red_c h0 a (U32.v i) /\ red_c h0 b (U32.v i) /\ live h1 a /\ modifies_1 a h0 h1
      /\ as_seq h1 a == fsum_spec (as_seq h0 a) (as_seq h0 b) (U32.v i)))
[@"substitute"]
inline_for_extraction let rec fsum_ a b i =
    let a0 = a.(0ul) in 
    let b0 = b.(0ul) in
    let a1 = a.(1ul) in 
    let b1 = b.(1ul) in
    let a2 = a.(2ul) in 
    let b2 = b.(2ul) in
    let a3 = a.(3ul) in 
    let b3 = b.(3ul) in
    let a4 = a.(4ul) in 
    let b4 = b.(4ul) in

    a.(0ul) <- a0 +^ b0;
    a.(1ul) <- a1 +^ b1;
    a.(2ul) <- a2 +^ b2;
    a.(3ul) <- a3 +^ b3;
    a.(4ul) <- a4 +^ b4
