module Hacl.Bignum.Crecip

open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Bignum.Fsquare
open Hacl.Bignum.Fmul


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
#set-options "--lax"

val crecip:
  out:felem ->
  z:felem{disjoint out z} ->
  Stack unit
  (requires (fun h -> live h out /\ live h z /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h z)))
  (ensures (fun h0 _ h1 -> live h1 out /\ modifies_1 out h0 h1
    /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h1 out)))
let crecip out z =
  push_frame();
  let buf = create limb_zero 20ul in
  let a  = Buffer.sub buf 0ul  5ul in
  let t0 = Buffer.sub buf 5ul  5ul in
  let b  = Buffer.sub buf 10ul 5ul in
  let c  = Buffer.sub buf 15ul 5ul in
  fsquare_times a z 1ul;
  fsquare_times t0 a 2ul;
  fmul b t0 z;
  fmul a b a;
  fsquare_times t0 a 1ul;
  fmul b t0 b;
  fsquare_times t0 b 5ul;
  fmul b t0 b;
  fsquare_times t0 b 10ul;
  fmul c t0 b;
  fsquare_times t0 c 20ul;
  fmul t0 t0 c;
  fsquare_times t0 t0 10ul;
  fmul b t0 b;
  fsquare_times t0 b 50ul;
  fmul c t0 b;
  fsquare_times t0 c 100ul;
  fmul t0 t0 c;
  fsquare_times t0 t0 50ul;
  fmul t0 t0 b;
  fsquare_times t0 t0 5ul;
  fmul out t0 a;
  pop_frame()
