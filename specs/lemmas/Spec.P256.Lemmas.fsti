module Spec.P256.Lemmas

open FStar.Mul
open Spec.P256.PointOps

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

val aff_point_at_inf_lemma (p:aff_point) :
  Lemma (aff_point_add p aff_point_at_inf = p)


val aff_point_add_assoc_lemma (p q s:aff_point) :
  Lemma (aff_point_add (aff_point_add p q) s == aff_point_add p (aff_point_add q s))


val aff_point_add_comm_lemma (p q:aff_point) :
  Lemma (aff_point_add p q = aff_point_add q p)


val to_aff_point_at_infinity_lemma: unit ->
  Lemma (to_aff_point point_at_inf == aff_point_at_inf)


val to_aff_point_add_lemma (p q:proj_point) :
  Lemma (to_aff_point (point_add p q) == aff_point_add (to_aff_point p) (to_aff_point q))


val to_aff_point_double_lemma (p:proj_point) :
  Lemma (to_aff_point (point_double p) == aff_point_add (to_aff_point p) (to_aff_point p))
