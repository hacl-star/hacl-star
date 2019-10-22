module Hacl.CTR.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

open Hacl.CTR

module Lemmas = Hacl.CTR.Lemmas


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 \
              --using_facts_from '-* +Prims +Lib.Sequence +FStar.Seq +Lib.IntTypes +Hacl.CTR +Hacl.CTR.Equiv +Math.Lemmas'"

///
///  Specification equivalence lemma
///

val ctr_equivalence:
    w:width_t
  -> k:key
  -> n:nonce
  -> ctr0:counter
  -> msg:seq uint8 ->
  Lemma
  (requires
    ctr0 + w <= max_size_t /\
    length msg / blocksize <= max_size_t /\ w * (length msg / (w * blocksize) + 1) <= max_size_t)
  (ensures
    ctr_v #w k n ctr0 msg `Seq.equal` ctr k n ctr0 msg)
