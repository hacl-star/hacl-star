module Hacl.Spec.K256.ECSM.Lemmas

open FStar.Mul

module M = Lib.NatMod
module LE = Lib.Exponentiation
module SE = Spec.Exponentiation
module S = Spec.K256
module LS = Spec.K256.Lemmas

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let aff_point_mul = S.aff_point_mul

assume
val lemma_order_of_curve_group (p:S.aff_point) :
  Lemma (aff_point_mul S.q p = S.aff_point_at_inf)


val lemma_proj_aff_id (p:S.aff_point) :
  Lemma (S.(to_aff_point (to_proj_point p)) = p)

let lemma_proj_aff_id p =
  let (px, py) = p in
  let (pX, pY, pZ) = S.to_proj_point p in
  assert (pX = px /\ pY = pY /\ pZ = S.one);
  let (rx, ry) = S.to_aff_point (pX, pY, pZ) in
  assert (rx = S.(pX /% pZ) /\ ry = S.(pY /% pZ));
  M.lemma_div_mod_prime_one #S.prime pX;
  M.lemma_div_mod_prime_one #S.prime pY;
  assert (rx = pX /\ ry = pY)


// TODO: what about point_at_infinity?
val lemma_point_mul (a:S.qelem) (p:S.proj_point) : Lemma
  (S.(to_aff_point (point_mul a p)) = aff_point_mul a (S.to_aff_point p))

let lemma_point_mul a p =
  SE.exp_fw_lemma S.mk_k256_concrete_ops p 256 a 4;
  LE.exp_fw_lemma S.mk_k256_comm_monoid (S.to_aff_point p) 256 a 4


val lemma_aff_point_mul_via_proj (a:S.qelem) (p:S.aff_point) : Lemma
  (S.(to_aff_point (point_mul a (to_proj_point p))) = aff_point_mul a p)

let lemma_aff_point_mul_via_proj a p =
  lemma_point_mul a (S.to_proj_point p);
  lemma_proj_aff_id p


(**
   Properties for Elliptic Curve Scalar Multiplication in affine coordinates
*)

val lemma_aff_point_mul_add (a b:nat) (p:S.aff_point) :
  Lemma (aff_point_mul (a + b) p = S.aff_point_add (aff_point_mul a p) (aff_point_mul b p))

let lemma_aff_point_mul_add a b p =
  LE.lemma_pow_add S.mk_k256_comm_monoid p a b


val lemma_aff_point_mul_mul (a b:nat) (p:S.aff_point) :
  Lemma (aff_point_mul (a * b) p = aff_point_mul b (aff_point_mul a p))

let lemma_aff_point_mul_mul a b p =
  LE.lemma_pow_mul S.mk_k256_comm_monoid p a b


val lemma_aff_point_mul_mul_add (a b c:nat) (p:S.aff_point) :
  Lemma (aff_point_mul (a * b + c) p =
    S.aff_point_add (aff_point_mul b (aff_point_mul a p)) (aff_point_mul c p))

let lemma_aff_point_mul_mul_add a b c p =
  lemma_aff_point_mul_add (a * b) c p;
  lemma_aff_point_mul_mul a b p


val lemma_aff_point_mul_modq (a:nat) (p:S.aff_point) :
  Lemma (aff_point_mul a p = aff_point_mul (a % S.q) p)

let lemma_aff_point_mul_modq a p =
  calc (==) {
    aff_point_mul a p;
    (==) { Math.Lemmas.euclidean_division_definition a S.q }
    aff_point_mul (a / S.q * S.q + a % S.q) p;
    (==) { lemma_aff_point_mul_add (a / S.q * S.q) (a % S.q) p }
    S.aff_point_add (aff_point_mul (a / S.q * S.q) p) (aff_point_mul (a % S.q) p);
    (==) { lemma_aff_point_mul_mul (a / S.q) S.q p }
    S.aff_point_add
      (aff_point_mul S.q (aff_point_mul (a / S.q) p))
      (aff_point_mul (a % S.q) p);
    (==) { lemma_order_of_curve_group (aff_point_mul (a / S.q) p) }
    S.aff_point_add S.aff_point_at_inf (aff_point_mul (a % S.q) p);
    (==) { LS.aff_point_add_comm_lemma S.aff_point_at_inf (aff_point_mul (a % S.q) p) }
    S.aff_point_add (aff_point_mul (a % S.q) p) S.aff_point_at_inf;
    (==) { LS.aff_point_at_inf_lemma (aff_point_mul (a % S.q) p) }
    aff_point_mul (a % S.q) p;
  }
