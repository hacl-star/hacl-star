module Hacl.CTR.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

open Hacl.CTR


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

///
///  Specification equivalence lemma
///

val ctr_equivalence: w:width_t -> k:key -> n:nonce -> c0:counter -> msg:seq uint8 -> Lemma
  (requires c0 + w <= max_size_t /\ length msg / blocksize + w - 1 <= max_size_t /\ length msg / (w * blocksize) <= max_size_t)
  (ensures  ctr_v #w k n c0 msg `Seq.equal` ctr k n c0 msg)
