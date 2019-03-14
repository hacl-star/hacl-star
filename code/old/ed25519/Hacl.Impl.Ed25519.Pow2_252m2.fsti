module Hacl.Impl.Ed25519.Pow2_252m2

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum25519

inline_for_extraction
val pow2_252m2:
  out:felem ->
  z:felem{disjoint out z} ->
  Stack unit
  (requires (fun h -> live h out /\ live h z /\ red_513 (as_seq h z)))
  (ensures (fun h0 _ h1 -> live h1 out /\ modifies_1 out h0 h1 /\ live h0 z
    /\ red_513 (as_seq h0 z)
    /\ seval (as_seq h1 out) == Spec.Curve25519.(seval (as_seq h0 z) ** ((prime + 3) / 8))
    /\ red_513 (as_seq h1 out)
  ))
