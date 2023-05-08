module Spec.EC.Projective.Lemmas

open FStar.Mul
open Spec.EC.Projective

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val lemma_aff_is_point_at_inf: k:curve -> p:proj_point k ->
  Lemma (let px, py, pz = p in
    is_aff_point_at_inf k (to_aff_point k p) == (pz = 0 || (px = 0 && py = 0)))


val lemma_proj_aff_id (k:curve) (p:aff_point k) :
  Lemma (to_aff_point k (to_proj_point k p) == p)


val to_aff_point_at_infinity_lemma: k:curve ->
  Lemma (to_aff_point k (point_at_inf k) == aff_point_at_inf k)


val to_aff_point_negate_lemma (k:curve) (p:proj_point k) :
  Lemma (to_aff_point k (point_negate k p) == aff_point_negate k (to_aff_point k p))
