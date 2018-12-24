module Hacl.Bignum.Fsum

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Spec.Bignum.Fsum

module U32 = FStar.UInt32

#reset-options "--max_fuel 0 --z3rlimit 20"

let red_c h (f:felem) ctr = live h f /\ red (as_seq h f) ctr

[@"substitute"]
val fsum_:
  a:felem ->
  b:felem{disjoint a b} ->
  Stack unit
    (requires (fun h -> red_c h a len /\ red_c h b len))
    (ensures (fun h0 _ h1 -> red_c h0 a len /\ red_c h0 b len /\ live h1 a /\ modifies_1 a h0 h1
      /\ as_seq h1 a == fsum_spec (as_seq h0 a) (as_seq h0 b)))
[@"substitute"]
let fsum_ a b =
  C.Compat.Loops.in_place_map2 a b clen (fun x y -> x +%^ y)
