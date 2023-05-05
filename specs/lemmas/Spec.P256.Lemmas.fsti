module Spec.P256.Lemmas

open FStar.Mul
open Spec.P256.PointOps
module EC = Spec.EC

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

(** The point addition and doubling formulas are taken from
    https://eprint.iacr.org/2015/1060.pdf. The correctness of
    the formulas is shown in Appendix A of the paper. Their
    verification in F* is left for the future. *)

// TODO: add `point_inv p = is_on_curve p || is_point_at_inf p`

val lemma_proj_aff_id (p:EC.aff_point p256) :
  Lemma (to_aff_point (to_proj_point p) == p)


val lemma_aff_is_point_at_inf: p:proj_point ->
  Lemma (let px, py, pz = p in
    EC.is_aff_point_at_inf p256 (to_aff_point p) == (pz = 0 || (px = 0 && py = 0)))


val to_aff_point_at_infinity_lemma: unit ->
  Lemma (to_aff_point point_at_inf == EC.aff_point_at_inf p256)


val to_aff_point_add_lemma (p q:proj_point) :
  Lemma (to_aff_point (point_add p q) ==
    EC.aff_point_add p256 (to_aff_point p) (to_aff_point q))


val to_aff_point_double_lemma (p:proj_point) :
  Lemma (to_aff_point (point_double p) ==
    EC.aff_point_add p256 (to_aff_point p) (to_aff_point p))
