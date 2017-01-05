module Hacl.Bignum.Fsum

open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Spec.Bignum.Fsum

module U32 = FStar.UInt32

#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

let fsum_pre h (f:felem) (f':felem) ctr =
  live h f /\ live h f' /\ fsum_spec_pre (as_seq h f) (as_seq h f') ctr

private val fsum_:
  a:felem ->
  b:felem{disjoint a b} ->
  i:ctr{U32.v i <= len} ->
  Stack unit
    (requires (fun h -> fsum_pre h a b (U32.v i)))
    (ensures (fun h0 _ h1 -> fsum_pre h0 a b (U32.v i) /\ live h1 a /\ modifies_1 a h0 h1
      /\ as_seq h1 a == fsum_spec (as_seq h0 a) (as_seq h0 b) (U32.v i)))
private let rec fsum_ a b i =
  if U32.(i =^ 0ul) then ()
  else (
    let i = U32.(i -^ 1ul) in
    let ai = a.(i) in let bi = b.(i) in
    Math.Lemmas.pow2_double_sum n;
    a.(i) <- ai +^ bi;
    fsum_ a b i
  )


inline_for_extraction val fsum:
  a:felem -> b:felem{disjoint a b} ->
  Stack unit
    (requires (fun h -> fsum_pre h a b len))
    (ensures (fun h0 _ h1 -> fsum_pre h0 a b len /\ live h1 a /\ modifies_1 a h0 h1
      /\ (to_field (as_seq h1 a) = to_field (as_seq h0 a) @+ to_field (as_seq h0 b))
    ))
inline_for_extraction let rec fsum a b =
  let h0 = ST.get() in
  lemma_fsum_field (as_seq h0 a) (as_seq h0 b);
  fsum_ a b clen
