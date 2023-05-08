module Spec.K256.Lemmas

open FStar.Mul

open Spec.K256.PointOps

module EC = Spec.EC.Projective
module LM = Lib.NatMod

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

val to_aff_point_add_lemma (p q:EC.proj_point k256) :
  Lemma (EC.to_aff_point k256 (point_add p q) ==
    EC.aff_point_add k256 (EC.to_aff_point k256 p) (EC.to_aff_point k256 q))


val to_aff_point_double_lemma (p:EC.proj_point k256) :
  Lemma (EC.to_aff_point k256 (point_double p) ==
    EC.aff_point_add k256 (EC.to_aff_point k256 p) (EC.to_aff_point k256 p))
