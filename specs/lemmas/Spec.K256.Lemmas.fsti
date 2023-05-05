module Spec.K256.Lemmas

open FStar.Mul

open Spec.K256.PointOps

module EC = Spec.EC
module LM = Lib.NatMod

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

val lemma_aff_is_point_at_inf: p:proj_point ->
  Lemma (let px, py, pz = p in
    EC.is_aff_point_at_inf k256 (to_aff_point p) == (pz = 0 || (px = 0 && py = 0)))


val lemma_proj_aff_id (p:EC.aff_point k256) :
  Lemma (to_aff_point (to_proj_point p) == p)


// TODO: mv to Spec.EC
val aff_point_negate_lemma (p:EC.aff_point k256) :
  Lemma (EC.aff_point_add k256 (aff_point_negate p) p == EC.aff_point_at_inf k256)


val to_aff_point_at_infinity_lemma: unit ->
  Lemma (to_aff_point point_at_inf == EC.aff_point_at_inf k256)


val to_aff_point_add_lemma (p q:proj_point) :
  Lemma (to_aff_point (point_add p q) == EC.aff_point_add k256 (to_aff_point p) (to_aff_point q))


val to_aff_point_double_lemma (p:proj_point) :
  Lemma (to_aff_point (point_double p) == EC.aff_point_add k256 (to_aff_point p) (to_aff_point p))


val to_aff_point_negate_lemma (p:proj_point) :
  Lemma (to_aff_point (point_negate p) == aff_point_negate (to_aff_point p))


// works when q < prime /\ prime < 2 * q
val ecdsa_verify_avoid_finv: p:proj_point{not (is_proj_point_at_inf p)} -> r:nat{0 < r /\ r < q} ->
  Lemma (let _X, _Y, _Z = p in
    (_X /% _Z % q = r) <==> ((r *% _Z = _X) || (r + q < prime && (r + q) *% _Z = _X)))
