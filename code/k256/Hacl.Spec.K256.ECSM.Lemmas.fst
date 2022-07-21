module Hacl.Spec.K256.ECSM.Lemmas

open FStar.Mul

module LE = Lib.Exponentiation
module S = Spec.K256
module LS = Spec.K256.Lemmas

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let aff_point_mul = S.aff_point_mul

assume
val lemma_order_of_curve_group (p:S.aff_point) :
  Lemma (aff_point_mul S.q p = S.aff_point_at_inf)

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
