module Hacl.Impl.P256.Scalar

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Felem

module S = Spec.P256

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

val qmod_short: x:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ eq_or_disjoint x res)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == as_nat h0 x % S.order)


val bn_is_lt_order_mask4: f:felem -> Stack uint64
  (requires fun h -> live h f)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    (if as_nat h0 f < S.order then v r = ones_v U64 else v r = 0))


val bn_is_lt_order_and_gt_zero_mask4: f:felem -> Stack uint64
  (requires fun h -> live h f)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    (if 0 < as_nat h0 f && as_nat h0 f < S.order then v r = ones_v U64 else v r = 0))


let qmont_R = pow2 256
let qmont_R_inv = S.modp_inv2_prime (pow2 256) S.order

// TODO: rename
let fromDomain_ (a:nat) : S.qelem = a * qmont_R_inv % S.order
let toDomain_   (a:nat) : S.qelem = a * qmont_R % S.order

// TODO: rm if we expose the defs of fromDomain and toDomain
val lemmaFromDomain: a:nat -> Lemma (fromDomain_ a == a * qmont_R_inv % S.order)
val lemmaToDomain:   a:nat -> Lemma (toDomain_ a == a * qmont_R % S.order)

val lemmaFromDomainToDomain: a:S.qelem -> Lemma (toDomain_ (fromDomain_ a) == a)
val lemmaToDomainFromDomain: a:S.qelem -> Lemma (fromDomain_ (toDomain_ a) == a)

let qmont_as_nat (h:mem) (a:felem) = fromDomain_ (as_nat h a)

// NOTE: changed precondition `eq_or_disjoint x y`
val qadd: x:felem -> y:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h x < S.order /\ as_nat h y < S.order)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == S.qadd (as_nat h0 x) (as_nat h0 y) /\
    qmont_as_nat h1 res == S.qadd (qmont_as_nat h0 x) (qmont_as_nat h0 y))


val qmul: a:felem -> b:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    eq_or_disjoint a b /\
    as_nat h a < S.order /\ as_nat h b < S.order)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = (as_nat h0 a * as_nat h0 b * qmont_R_inv) % S.order /\
    qmont_as_nat h1 res = S.qmul (qmont_as_nat h0 a) (qmont_as_nat h0 b))


// rename
val fromDomainImpl: a:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ as_nat h a < S.order)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.order /\
    as_nat h1 res == qmont_as_nat h0 a)
