module Hacl.Spec.P256.Montgomery

open FStar.Mul
open Lib.IntTypes

module S = Spec.P256
module M = Lib.NatMod
module LSeq = Lib.Sequence

module BD = Hacl.Spec.Bignum.Definitions
module SBM = Hacl.Spec.Bignum.Montgomery

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val mont_cancel_lemma_gen (n:pos) (mont_R mont_R_inv a b:nat) : Lemma
  (requires mont_R_inv * mont_R % n = 1)
  (ensures (a * mont_R % n * b * mont_R_inv) % n = a * b % n)


///  Montgomery arithmetic for a base field

let fmont_R = pow2 256
val fmont_R_inv : pos

val mul_fmont_R_and_R_inv_is_one: unit -> Lemma (fmont_R * fmont_R_inv % S.prime = 1)

let from_mont (a:int) : S.felem = a * fmont_R_inv % S.prime
let to_mont   (a:int) : S.felem = a * fmont_R % S.prime

val bn_mont_reduction_lemma: x:LSeq.lseq uint64 8 -> n:LSeq.lseq uint64 4 -> Lemma
  (requires BD.bn_v n = S.prime /\ BD.bn_v x < S.prime * S.prime)
  (ensures  BD.bn_v (SBM.bn_mont_reduction n (u64 1) x) == BD.bn_v x * fmont_R_inv % S.prime)

val lemma_from_mont_zero: a:S.felem -> Lemma (from_mont a == 0 <==> a == 0)
val lemma_to_from_mont_id: a:S.felem -> Lemma (from_mont (to_mont a) == a)
val lemma_from_to_mont_id: a:S.felem -> Lemma (to_mont (from_mont a) == a)

val fmont_mul_lemma: a:S.felem -> b:S.felem ->
  Lemma (S.fmul (from_mont a) (from_mont b) = from_mont ((a * b * fmont_R_inv) % S.prime))

val fmont_add_lemma: a:S.felem -> b:S.felem ->
  Lemma (S.fadd (from_mont a) (from_mont b) = from_mont ((a + b) % S.prime))

val fmont_sub_lemma: a:S.felem -> b:S.felem ->
  Lemma (S.fsub (from_mont a) (from_mont b) = from_mont ((a - b) % S.prime))


///  Montgomery arithmetic for a scalar field

let qmont_R = pow2 256
val qmont_R_inv : pos

val mul_qmont_R_and_R_inv_is_one: unit -> Lemma (qmont_R * qmont_R_inv % S.order = 1)

let from_qmont (a:nat) : S.qelem = a * qmont_R_inv % S.order
let to_qmont   (a:nat) : S.qelem = a * qmont_R % S.order

val bn_qmont_reduction_lemma: x:LSeq.lseq uint64 8 -> n:LSeq.lseq uint64 4 -> Lemma
  (requires BD.bn_v n = S.order /\ BD.bn_v x < S.order * S.order)
  (ensures  BD.bn_v (SBM.bn_mont_reduction n (u64 0xccd1c8aaee00bc4f) x) ==
    BD.bn_v x * qmont_R_inv % S.order)

val lemma_to_from_qmont_id: a:S.qelem -> Lemma (from_qmont (to_qmont a) == a)
val lemma_from_to_qmont_id: a:S.qelem -> Lemma (to_qmont (from_qmont a) == a)

val qmont_add_lemma: a:S.qelem -> b:S.qelem ->
  Lemma (S.qadd (from_qmont a) (from_qmont b) = from_qmont ((a + b) % S.order))

val qmont_mul_lemma: a:S.qelem -> b:S.qelem ->
  Lemma (S.qmul (from_qmont a) (from_qmont b) = from_qmont ((a * b * qmont_R_inv) % S.order))

val qmont_inv_lemma: k:S.qelem ->
  Lemma (S.qinv (from_qmont k) == to_qmont (S.qinv k))


val qmont_inv_mul_lemma: s:S.qelem -> sinv:S.qelem -> b:S.qelem -> Lemma
  (requires from_qmont sinv == S.qinv (from_qmont s)) // post-condition of qinv
  (ensures  S.qinv s * b % S.order == from_qmont (sinv * from_qmont b))


val lemma_ecdsa_sign_s (k kinv r d_a m:S.qelem) : Lemma
  (requires from_qmont kinv == to_qmont (S.qinv k))
  (ensures (let s = (from_qmont m + from_qmont (r * d_a)) % S.order in
   from_qmont (kinv * s) == S.qmul (S.qinv k) (S.qadd m (S.qmul r d_a))))
