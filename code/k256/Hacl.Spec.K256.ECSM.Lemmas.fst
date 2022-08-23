module Hacl.Spec.K256.ECSM.Lemmas

open FStar.Mul

module M = Lib.NatMod
module LE = Lib.Exponentiation
module SE = Spec.Exponentiation

module S = Spec.K256
module LS = Spec.K256.Lemmas

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

// [a]P in affine coordinates
let aff_point_mul = S.aff_point_mul

// [a]P in affine coordinates
let aff_point_mul_neg (a:int) (p:S.aff_point) : S.aff_point =
  LE.pow_neg S.mk_k256_abelian_group p a


assume
val lemma_order_of_curve_group (p:S.aff_point) :
  Lemma (aff_point_mul S.q p == S.aff_point_at_inf)


val lemma_proj_aff_id (p:S.aff_point) :
  Lemma (S.(to_aff_point (to_proj_point p)) == p)

let lemma_proj_aff_id p =
  let (px, py) = p in
  let (pX, pY, pZ) = S.to_proj_point p in
  assert (pX = px /\ pY = pY /\ pZ = S.one);
  let (rx, ry) = S.to_aff_point (pX, pY, pZ) in
  assert (rx = S.(pX /% pZ) /\ ry = S.(pY /% pZ));
  M.lemma_div_mod_prime_one #S.prime pX;
  M.lemma_div_mod_prime_one #S.prime pY;
  assert (rx = pX /\ ry = pY)


// // TODO: what about point_at_infinity?
// val lemma_point_mul (a:S.qelem) (p:S.proj_point) : Lemma
//   (S.(to_aff_point (point_mul a p)) == aff_point_mul a (S.to_aff_point p))

// let lemma_point_mul a p =
//   SE.exp_fw_lemma S.mk_k256_concrete_ops p 256 a 4;
//   LE.exp_fw_lemma S.mk_k256_comm_monoid (S.to_aff_point p) 256 a 4


// val lemma_aff_point_mul_via_proj (a:S.qelem) (p:S.aff_point) : Lemma
//   (S.(to_aff_point (point_mul a (to_proj_point p))) == aff_point_mul a p)

// let lemma_aff_point_mul_via_proj a p =
//   lemma_point_mul a (S.to_proj_point p);
//   lemma_proj_aff_id p


(**
   Properties for Elliptic Curve Scalar Multiplication in affine coordinates
*)

val lemma_aff_point_mul_neg_add (a b:int) (p:S.aff_point) :
  Lemma (aff_point_mul_neg (a + b) p ==
    S.aff_point_add (aff_point_mul_neg a p) (aff_point_mul_neg b p))

let lemma_aff_point_mul_neg_add a b p =
  LE.lemma_pow_neg_add S.mk_k256_abelian_group p a b


val lemma_aff_point_mul_neg_mul (a b:int) (p:S.aff_point) :
  Lemma (aff_point_mul_neg (a * b) p == aff_point_mul_neg b (aff_point_mul_neg a p))

let lemma_aff_point_mul_neg_mul a b p =
  LE.lemma_pow_neg_mul S.mk_k256_abelian_group p a b


val lemma_aff_point_mul_neg_mul_add (a b c:int) (p:S.aff_point) :
  Lemma (aff_point_mul_neg (a * b + c) p ==
    S.aff_point_add (aff_point_mul_neg b (aff_point_mul_neg a p)) (aff_point_mul_neg c p))

let lemma_aff_point_mul_neg_mul_add a b c p =
  lemma_aff_point_mul_neg_add (a * b) c p;
  lemma_aff_point_mul_neg_mul a b p


val lemma_aff_point_mul_neg_modq (a:int) (p:S.aff_point) :
  Lemma (aff_point_mul_neg a p == aff_point_mul (a % S.q) p)

let lemma_aff_point_mul_neg_modq a p =
  calc (==) {
    aff_point_mul_neg a p;
    (==) { Math.Lemmas.euclidean_division_definition a S.q }
    aff_point_mul_neg (a / S.q * S.q + a % S.q) p;
    (==) { lemma_aff_point_mul_neg_add (a / S.q * S.q) (a % S.q) p }
    S.aff_point_add (aff_point_mul_neg (a / S.q * S.q) p) (aff_point_mul_neg (a % S.q) p);
    (==) { lemma_aff_point_mul_neg_mul (a / S.q) S.q p }
    S.aff_point_add
      (aff_point_mul S.q (aff_point_mul_neg (a / S.q) p))
      (aff_point_mul (a % S.q) p);
    (==) { lemma_order_of_curve_group (aff_point_mul_neg (a / S.q) p) }
    S.aff_point_add S.aff_point_at_inf (aff_point_mul (a % S.q) p);
    (==) { LS.aff_point_add_comm_lemma S.aff_point_at_inf (aff_point_mul (a % S.q) p) }
    S.aff_point_add (aff_point_mul (a % S.q) p) S.aff_point_at_inf;
    (==) { LS.aff_point_at_inf_lemma (aff_point_mul (a % S.q) p) }
    aff_point_mul (a % S.q) p;
  }

//-----------------------------------

(**
    ECDSA-verify using ECSM in affine coordinates
*)

open Lib.Sequence
open Lib.ByteSequence

// TODO: a_spec = x:S.aff_point{S.is_on_curve x \/ S.is_aff_point_at_inf x}
let aff_mk_to_k256_cm : SE.to_comm_monoid S.aff_point = {
  SE.a_spec = S.aff_point;
  SE.comm_monoid = S.mk_k256_comm_monoid;
  SE.refl = (fun (x:S.aff_point) -> x);
}

val aff_point_at_inf_c: SE.one_st S.aff_point aff_mk_to_k256_cm
let aff_point_at_inf_c _ = S.aff_point_at_inf

val aff_point_add_c : SE.mul_st S.aff_point aff_mk_to_k256_cm
let aff_point_add_c p q = S.aff_point_add p q

val aff_point_double_c : SE.sqr_st S.aff_point aff_mk_to_k256_cm
let aff_point_double_c p = S.aff_point_add p p

let aff_mk_k256_concrete_ops : SE.concrete_ops S.aff_point = {
  SE.to = aff_mk_to_k256_cm;
  SE.one = aff_point_at_inf_c;
  SE.mul = aff_point_add_c;
  SE.sqr = aff_point_double_c;
}
