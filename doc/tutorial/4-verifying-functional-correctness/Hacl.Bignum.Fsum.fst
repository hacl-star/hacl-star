module Hacl.Bignum.Fsum

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.HyperStack
open FStar.Buffer
open FStar.UInt64

open Hacl.Spec.Bignum.Fsum

module U32 = FStar.UInt32

#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

private val fsum_:
  a:felem ->
  b:felem{disjoint a b} ->
  i:U32.t{U32.v i <= len} ->
  Stack unit
    (requires (fun h -> live h a /\ live h b
      /\ fsum_spec_pre (as_seq h a) (as_seq h b) (U32.v i)
    ))
    (ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\ live h1 a
      /\ fsum_spec_pre (as_seq h0 a) (as_seq h0 b) (U32.v i)
      /\ modifies_1 a h0 h1
      /\ as_seq h1 a == fsum_spec (as_seq h0 a) (as_seq h0 b) (U32.v i)))
private let rec fsum_ a b i =
  if U32.(i =^ 0ul) then ()
  else (
    let i = U32.(i -^ 1ul) in
    let ai = a.(i) in let bi = b.(i) in
    Math.Lemmas.pow2_double_sum 64;
    a.(i) <- ai +^ bi;
    fsum_ a b i
  )


inline_for_extraction val fsum:
  a:felem -> b:felem{disjoint a b} ->
  Stack unit
    (requires (fun h -> live h a /\ live h b /\ fsum_spec_pre (as_seq h a) (as_seq h b) len))
    (ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\ fsum_spec_pre (as_seq h0 a) (as_seq h0 b) len
      /\ live h1 a /\ modifies_1 a h0 h1
      /\ (to_field (as_seq h1 a) = to_field (as_seq h0 a) @+ to_field (as_seq h0 b))
    ))
inline_for_extraction let rec fsum a b =
  let h0 = ST.get() in
  lemma_fsum_field (as_seq h0 a) (as_seq h0 b);
  fsum_ a b 5ul
