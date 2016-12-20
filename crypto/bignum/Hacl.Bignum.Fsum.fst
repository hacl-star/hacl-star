module Hacl.Bignum.Fsum

open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Spec.Bignum.Fsum

module U32 = FStar.UInt32

#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

let red_c h (f:felem) ctr = live h f /\ red (as_seq h f) ctr

val fsum_:
  a:felem ->
  b:felem{disjoint a b} ->
  i:ctr{U32.v i <= len} ->
  Stack unit
    (requires (fun h -> red_c h a (U32.v i) /\ red_c h b (U32.v i)))
    (ensures (fun h0 _ h1 -> red_c h0 a (U32.v i) /\ red_c h0 b (U32.v i) /\ live h1 a /\ modifies_1 a h0 h1
      /\ as_seq h1 a == fsum_spec (as_seq h0 a) (as_seq h0 b) (U32.v i)))
let rec fsum_ a b i =
  if U32.(i =^ 0ul) then ()
  else (
    let i = U32.(i -^ 1ul) in
    let ai = a.(i) in let bi = b.(i) in
    Math.Lemmas.pow2_double_sum n;
    a.(i) <- ai +^ bi;
    fsum_ a b i
  )
