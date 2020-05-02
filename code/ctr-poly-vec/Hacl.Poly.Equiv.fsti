module Hacl.Poly.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Hacl.Poly

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

///
///  Specification equivalence lemma
///

val poly_equivalence: #w:lanes{w > 0} -> text:bytes{w * blocksize <= length text} -> acc:felem -> r:felem -> Lemma
  (poly_update_v #w text acc r == poly_update text acc r)
