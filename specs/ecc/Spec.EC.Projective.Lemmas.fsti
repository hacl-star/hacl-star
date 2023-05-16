module Spec.EC.Projective.Lemmas

open FStar.Mul
open Spec.EC.Projective

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

// works when q < prime /\ prime < 2 * q
val ecdsa_verify_avoid_finv:
    k:curve{k.order < k.prime /\ k.prime < 2 * k.order}
  -> p:proj_point k{not (is_point_at_inf k p)}
  -> r:nat{0 < r /\ r < k.order} ->
  Lemma (let _X, _Y, _Z = p in
    (fmul k _X (finv k _Z) % k.order = r) <==>
    ((fmul k r _Z = _X) || (r + k.order < k.prime && fmul k (r + k.order) _Z = _X)))


val point_inv_is_point_at_inf: k:curve -> p:proj_point k -> Lemma
  (requires point_inv k p /\ is_point_at_inf k p)
  (ensures  (let px, _, _ = p in px = zero k))


val lemma_is_point_at_inf: k:curve -> p:proj_point k -> Lemma
  (requires is_point_at_inf k p)
  (ensures  to_aff_point k p = aff_point_at_inf k)


val point_inv_ec_lemma: k:curve -> p:proj_point k -> Lemma
  (requires not (is_point_at_inf k p))
  (ensures  point_inv k p <==> is_on_curve k (to_aff_point k p))


val point_inv_lemma: k:curve -> p:proj_point k -> Lemma
  (requires point_inv k p)
  (ensures  point_inv_to_aff k p)


val lemma_aff_is_point_at_inf: k:curve -> p:proj_point k ->
  Lemma (let px, py, pz = p in
    is_aff_point_at_inf k (to_aff_point k p) == (pz = 0 || (px = 0 && py = 0)))


val lemma_aff_is_point_at_inf_c: k:curve -> p:proj_point k{point_inv k p} ->
  Lemma (let px, py, pz = p in is_aff_point_at_inf k (to_aff_point k p) == (pz = 0))


val lemma_proj_aff_id (k:curve) (p:aff_point k) :
  Lemma (to_aff_point k (to_proj_point k p) == p)

//---------------

val lemma_point_at_inf_c: k:curve -> 
  Lemma (point_inv k (point_at_inf k))


val lemma_to_aff_point_c: k:curve -> p:proj_point_c k ->
  Lemma (aff_point_inv k (to_aff_point k p))


val lemma_to_proj_point_c: k:curve -> p:aff_point_c k ->
  Lemma (point_inv k (to_proj_point k p))

//----------------

val to_aff_point_at_infinity_lemma: k:curve ->
  Lemma (to_aff_point k (point_at_inf k) == aff_point_at_inf k)


val to_aff_point_negate_lemma (k:curve) (p:proj_point_c k) :
  Lemma (point_inv k (point_negate k p) /\
    to_aff_point k (point_negate k p) == aff_point_negate k (to_aff_point k p))


(** The point addition and doubling formulas are taken from
    https://eprint.iacr.org/2015/1060.pdf. The correctness of
    the formulas is shown in Appendix A of the paper. Their
    verification in F* is left for the future. *)

val to_aff_point_add_lemma_a3 (k:curve{k.coeff_a = (-3) % k.prime}) (p q:proj_point_c k) :
  Lemma (point_inv k (point_add_a3 k p q) /\
    to_aff_point k (point_add_a3 k p q) == aff_point_add k (to_aff_point k p) (to_aff_point k q))


val to_aff_point_double_lemma_a3 (k:curve{k.coeff_a = (-3) % k.prime}) (p:proj_point_c k) :
  Lemma (point_inv k (point_double_a3 k p) /\
    to_aff_point k (point_double_a3 k p) == aff_point_add k (to_aff_point k p) (to_aff_point k p))


val to_aff_point_add_lemma_a0 (k:curve{k.coeff_a = 0}) (p q:proj_point_c k) :
  Lemma (point_inv k (point_add_a0 k p q) /\
    to_aff_point k (point_add_a0 k p q) == aff_point_add k (to_aff_point k p) (to_aff_point k q))


val to_aff_point_double_lemma_a0 (k:curve{k.coeff_a = 0}) (p:proj_point_c k) :
  Lemma (point_inv k (point_double_a0 k p) /\
    to_aff_point k (point_double_a0 k p) == aff_point_add k (to_aff_point k p) (to_aff_point k p))
