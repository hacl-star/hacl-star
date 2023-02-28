module Hacl.Impl.P256.Scalar //before: Hacl.Impl.ECDSA.MontgomeryMultiplication

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.ECDSA
module S = Spec.P256

open Hacl.Spec.P256.Felem

//#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

val reduction_prime_2prime_order: x:felem -> result:felem -> Stack unit
  (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    as_nat h1 result == as_nat h0 x % S.order)


noextract
val fromDomain_: a:nat -> Tot (r:nat{r < S.order})

noextract
val toDomain_: a:nat -> Tot nat


val lemmaFromDomain: a:nat ->
  Lemma ((a * S.modp_inv2_prime (pow2 256) S.order) % S.order == fromDomain_ a)

val lemmaToDomain: a:nat -> Lemma ((a * pow2 256) % S.order == toDomain_ a)

val lemmaFromDomainToDomain: a:nat{a < S.order} -> Lemma (toDomain_ (fromDomain_ a) == a)

val lemmaToDomainFromDomain: a:nat{a < S.order} -> Lemma (fromDomain_ (toDomain_ a) == a)


val montgomery_multiplication_ecdsa_module: a:felem -> b:felem -> result:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h result /\
    eq_or_disjoint a b /\
    as_nat h a < S.order /\ as_nat h b < S.order)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    as_nat h1 result = (as_nat h0 a * as_nat h0 b * S.modp_inv2_prime (pow2 256) S.order) % S.order /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b) % S.order))


inline_for_extraction noextract
val felem_add: arg1:felem -> arg2:felem -> out:felem -> Stack unit
  (requires fun h0 ->
    live h0 arg1 /\ live h0 arg2 /\ live h0 out /\
    eq_or_disjoint arg1 out /\ eq_or_disjoint arg2 out /\
    as_nat h0 arg1 < S.order /\ as_nat h0 arg2 < S.order)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out == (as_nat h0 arg1 + as_nat h0 arg2) % S.order)

val lemma_felem_add: a:nat -> b:nat -> Lemma ((fromDomain_ a + fromDomain_ b) % S.order = fromDomain_ (a + b))


val fromDomainImpl: a:felem -> result:felem -> Stack unit
  (requires fun h -> live h a /\ live h result /\ as_nat h a < S.order)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
     as_nat h1 result < S.order /\ as_nat h1 result == fromDomain_ (as_nat h0 a))