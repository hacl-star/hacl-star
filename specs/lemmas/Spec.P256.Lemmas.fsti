module Spec.P256.Lemmas

open FStar.Mul
open Spec.P256.PointOps

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

(** The point addition and doubling formulas are taken from
    https://eprint.iacr.org/2015/1060.pdf. The correctness of
    the formulas is shown in Appendix A of the paper. Their
    verification in F* is left for the future. *)

// TODO: add `point_inv p = is_on_curve p || is_point_at_inf p`

val prime_lemma: c:curve_params ->
    Lemma (FStar.Math.Euclid.is_prime c.prime /\
           FStar.Math.Euclid.is_prime c.order)

val lemma_exp_prime: p:nat{FStar.Math.Euclid.is_prime p} -> x:nat{x < p} ->
  Lemma (Lib.NatMod.pow_mod #p x (p-1) == 1)

val lemma_exp_inv_prime: p:nat{FStar.Math.Euclid.is_prime p} ->
  x:nat{x < p} -> y:nat ->
  Lemma (x * y % p == 1 ==> Lib.NatMod.pow_mod #p x (p-2) == y % p)

val lemma_aff_is_point_at_inf: {| curve_params |} -> p:proj_point ->
  Lemma (let px, py, pz = p in
    is_aff_point_at_inf (to_aff_point p) == (pz = 0 || (px = 0 && py = 0)))


val aff_point_at_inf_lemma {| curve_params |}  (p:aff_point) :
  Lemma (aff_point_add p aff_point_at_inf = p)


val aff_point_add_assoc_lemma {| curve_params |} (p q s:aff_point) :
  Lemma (aff_point_add (aff_point_add p q) s == aff_point_add p (aff_point_add q s))


val aff_point_add_comm_lemma {| curve_params |} (p q:aff_point) :
  Lemma (aff_point_add p q = aff_point_add q p)


val to_aff_point_at_infinity_lemma {| curve_params |} :
  Lemma (to_aff_point point_at_inf == aff_point_at_inf)


val to_aff_point_add_lemma {| curve_params |} (p q:proj_point) :
  Lemma (to_aff_point (point_add p q) == aff_point_add (to_aff_point p) (to_aff_point q))


val to_aff_point_double_lemma {| curve_params |} (p:proj_point) :
  Lemma (to_aff_point (point_double p) == aff_point_add (to_aff_point p) (to_aff_point p))
