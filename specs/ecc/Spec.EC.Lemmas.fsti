module Spec.EC.Lemmas

open FStar.Mul
open Spec.EC

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

val aff_point_add_inv_lemma: k:curve -> p:aff_point k -> q:aff_point k -> Lemma
  (requires aff_point_inv k p /\ aff_point_inv k q)
  (ensures  aff_point_inv k (aff_point_add k p q))

val aff_point_negate_on_curve_lemma: k:curve -> p:aff_point k -> Lemma
  (requires is_on_curve k p)
  (ensures  is_on_curve k (aff_point_negate k p))

val aff_point_negate_inv_lemma: k:curve -> p:aff_point k -> Lemma
  (requires aff_point_inv k p)
  (ensures  aff_point_inv k (aff_point_negate k p))


val aff_point_at_inf_lemma (k:curve) (p:aff_point_c k) :
  Lemma (aff_point_add k p (aff_point_at_inf k) = p)


val aff_point_add_assoc_lemma (k:curve) (p q s:aff_point_c k) :
  Lemma (aff_point_add k (aff_point_add k p q) s == aff_point_add k p (aff_point_add k q s))


val aff_point_add_comm_lemma (k:curve) (p q:aff_point_c k) :
  Lemma (aff_point_add k p q = aff_point_add k q p)


val aff_point_negate_lemma (k:curve) (p:aff_point_c k) :
  Lemma (aff_point_add k (aff_point_negate k p) p == aff_point_at_inf k)
