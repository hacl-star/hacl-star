module Hacl.Bignum.Fsquare

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Spec.Bignum.Fsquare


val fsquare_times:
  output:felem ->
  input:felem{disjoint output input} ->
  count:FStar.UInt32.t{FStar.UInt32.v count > 0} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ fsquare_pre (as_seq h input)))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h1 output /\ live h0 input /\ modifies_1 output h0 h1
      /\ fsquare_pre (as_seq h0 input)
      /\ (as_seq h1 output) == fsquare_times_tot (as_seq h0 input) (FStar.UInt32.v count)))
