module Spec.K256.Lemmas

open FStar.Mul

open Spec.K256.PointOps

module EC = Spec.EC.Projective
module LM = Lib.NatMod

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

// TODO: mv to Spec.EC
val aff_point_negate_lemma (p:EC.aff_point k256) :
  Lemma (EC.aff_point_add k256 (aff_point_negate p) p == EC.aff_point_at_inf k256)


val to_aff_point_at_infinity_lemma: unit ->
  Lemma (EC.to_aff_point k256 (EC.point_at_inf k256) == EC.aff_point_at_inf k256)


val to_aff_point_add_lemma (p q:EC.proj_point k256) :
  Lemma (EC.to_aff_point k256 (point_add p q) ==
    EC.aff_point_add k256 (EC.to_aff_point k256 p) (EC.to_aff_point k256 q))


val to_aff_point_double_lemma (p:EC.proj_point k256) :
  Lemma (EC.to_aff_point k256 (point_double p) ==
    EC.aff_point_add k256 (EC.to_aff_point k256 p) (EC.to_aff_point k256 p))


val to_aff_point_negate_lemma (p:EC.proj_point k256) :
  Lemma (EC.to_aff_point k256 (point_negate p) == aff_point_negate (EC.to_aff_point k256 p))


// works when q < prime /\ prime < 2 * q
val ecdsa_verify_avoid_finv: p:EC.proj_point k256{not (EC.is_point_at_inf k256 p)}
  -> r:nat{0 < r /\ r < q} ->
  Lemma (let _X, _Y, _Z = p in
    (_X /% _Z % q = r) <==> ((r *% _Z = _X) || (r + q < prime && (r + q) *% _Z = _X)))
