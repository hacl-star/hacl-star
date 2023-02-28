module Hacl.Impl.P256.Scalar

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Felem

module S = Spec.P256
module SD = Spec.ECDSA

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

val qmod_short: x:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ eq_or_disjoint x res)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == as_nat h0 x % S.order)

let qmont_R = pow2 256
let qmont_R_inv = S.modp_inv2_prime (pow2 256) S.order

let fromDomain_ (a:nat) : S.qelem = a * qmont_R_inv % S.order
let toDomain_   (a:nat) : S.qelem = a * qmont_R % S.order

// TODO: rm if we expose the defs of fromDomain and toDomain
val lemmaFromDomain: a:nat -> Lemma (fromDomain_ a == a * qmont_R_inv % S.order)
val lemmaToDomain:   a:nat -> Lemma (toDomain_ a == a * qmont_R % S.order)

val lemmaFromDomainToDomain: a:S.qelem -> Lemma (toDomain_ (fromDomain_ a) == a)
val lemmaToDomainFromDomain: a:S.qelem -> Lemma (fromDomain_ (toDomain_ a) == a)


// rename with qmul
val montgomery_multiplication_ecdsa_module: a:felem -> b:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    eq_or_disjoint a b /\
    as_nat h a < S.order /\ as_nat h b < S.order)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = (as_nat h0 a * as_nat h0 b * qmont_R_inv) % S.order /\
    as_nat h1 res = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b) % S.order))

// rename with qadd
// NOTE: changed precondition `eq_or_disjoint x y`
val felem_add: x:felem -> y:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h x < S.order /\ as_nat h y < S.order)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == (as_nat h0 x + as_nat h0 y) % S.order)

// rename with qadd_lemma
val lemma_felem_add: a:nat -> b:nat ->
  Lemma ((fromDomain_ a + fromDomain_ b) % S.order = fromDomain_ (a + b))


// rename
val fromDomainImpl: a:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ as_nat h a < S.order)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
     as_nat h1 res < S.order /\
     as_nat h1 res == fromDomain_ (as_nat h0 a))
