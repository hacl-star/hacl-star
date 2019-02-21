module Hacl.Bignum.Fscalar

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Spec.Bignum.Fscalar

module U32 = FStar.UInt32

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"


[@"substitute"]
val fscalar:
  output:felem_wide ->
  input:felem{disjoint output input} ->
  s:limb ->
  Stack unit
    (requires (fun h -> live h output /\ live h input))
    (ensures  (fun h0 _ h1 -> live h0 output /\ live h0 input /\ live h1 output /\ modifies_1 output h0 h1
      /\ as_seq h1 output == fscalar_spec (as_seq h0 input) s))
[@"substitute"]
let fscalar output b s =
  C.Compat.Loops.map output b clen (fun x -> Hacl.Bignum.Wide.mul_wide x s)
