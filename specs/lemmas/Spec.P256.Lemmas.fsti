module Spec.P256.Lemmas

open FStar.Mul
open Spec.P256.PointOps

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

(** The point addition and doubling formulas are taken from
    https://eprint.iacr.org/2015/1060.pdf. The correctness of
    the formulas is shown in Appendix A of the paper. Their
    verification in F* is left for the future.

    The group-law lemmas hold only for valid points: `aff_point_inv` and
    `point_inv` (Spec.P256.PointOps). For points off the curve, they are
    false (github.com/hacl-star/hacl-star/issues/1079). *)

val prime_lemma: unit -> Lemma (FStar.Math.Euclid.is_prime prime)

val lemma_aff_is_point_at_inf: p:proj_point ->
  Lemma (let px, py, pz = p in
    is_aff_point_at_inf (to_aff_point p) == (pz = 0 || (px = 0 && py = 0)))


/// Valid points

val point_inv_lemma (p:proj_point) : Lemma
  (point_inv p <==>
    (let (x, y, z) = p in
     if z = 0 then x = 0 /\ y <> 0 else is_on_curve (to_aff_point p)))


val aff_point_at_inf_inv: unit -> Lemma (aff_point_inv aff_point_at_inf)


val point_at_inf_inv: unit -> Lemma (point_inv point_at_inf)


val base_point_inv: unit ->
  Lemma (point_inv base_point /\ to_aff_point base_point == (g_x, g_y) /\ aff_point_inv (g_x, g_y))


val to_aff_point_inv (p:proj_point) : Lemma
  (requires point_inv p)
  (ensures  aff_point_inv (to_aff_point p))


val to_proj_point_inv (p:aff_point) : Lemma
  (requires is_on_curve p)
  (ensures  point_inv (to_proj_point p) /\ to_aff_point (to_proj_point p) == p)


val load_point_inv (b:Lib.ByteSequence.lbytes 64) :
  Lemma (Some? (load_point b) ==> point_inv (Some?.v (load_point b)))


/// Affine group law

val aff_point_at_inf_lemma (p:aff_point) :
  Lemma (aff_point_add p aff_point_at_inf = p)


val aff_point_add_inv_lemma (p q:aff_point) : Lemma
  (requires aff_point_inv p /\ aff_point_inv q)
  (ensures  aff_point_inv (aff_point_add p q))


val aff_point_add_assoc_lemma (p q s:aff_point) : Lemma
  (requires aff_point_inv p /\ aff_point_inv q /\ aff_point_inv s)
  (ensures  aff_point_add (aff_point_add p q) s == aff_point_add p (aff_point_add q s))


val aff_point_add_comm_lemma (p q:aff_point) :
  Lemma (aff_point_add p q = aff_point_add q p)


/// Projective formulas

val to_aff_point_at_infinity_lemma: unit ->
  Lemma (to_aff_point point_at_inf == aff_point_at_inf)


val to_aff_point_add_lemma (p q:proj_point) : Lemma
  (requires point_inv p /\ point_inv q)
  (ensures (let r = point_add p q in point_inv r /\
    to_aff_point r == aff_point_add (to_aff_point p) (to_aff_point q)))


val to_aff_point_double_lemma (p:proj_point) : Lemma
  (requires point_inv p)
  (ensures (let r = point_double p in point_inv r /\
    to_aff_point r == aff_point_add (to_aff_point p) (to_aff_point p)))
