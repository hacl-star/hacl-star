module Spec.EC.Lemmas

open FStar.Mul
open Spec.EC

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

// TODO: add `point_inv p = is_on_curve p || is_point_at_inf p`

val aff_point_at_inf_lemma (k:curve) (p:aff_point k) :
  Lemma (aff_point_add k p (aff_point_at_inf k) = p)


val aff_point_add_assoc_lemma (k:curve) (p q s:aff_point k) :
  Lemma (aff_point_add k (aff_point_add k p q) s == aff_point_add k p (aff_point_add k q s))


val aff_point_add_comm_lemma (k:curve) (p q:aff_point k) :
  Lemma (aff_point_add k p q = aff_point_add k q p)


val aff_point_negate_lemma (k:curve) (p:aff_point k) :
  Lemma (aff_point_add k (aff_point_negate k p) p == aff_point_at_inf k)
