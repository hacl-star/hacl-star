module Spec.P256.Lemmas

open FStar.Mul
open Spec.P256.PointOps
module EC = Spec.EC.Projective

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

(** The point addition and doubling formulas are taken from
    https://eprint.iacr.org/2015/1060.pdf. The correctness of
    the formulas is shown in Appendix A of the paper. Their
    verification in F* is left for the future. *)

// TODO: add `point_inv p = is_on_curve p || is_point_at_inf p`

val to_aff_point_at_infinity_lemma: unit ->
  Lemma (EC.to_aff_point p256 (EC.point_at_inf p256) == EC.aff_point_at_inf p256)


val to_aff_point_add_lemma (p q:EC.proj_point p256) :
  Lemma (EC.to_aff_point p256 (point_add p q) ==
    EC.aff_point_add p256 (EC.to_aff_point p256 p) (EC.to_aff_point p256 q))


val to_aff_point_double_lemma (p:EC.proj_point p256) :
  Lemma (EC.to_aff_point p256 (point_double p) ==
    EC.aff_point_add p256 (EC.to_aff_point p256 p) (EC.to_aff_point p256 p))
