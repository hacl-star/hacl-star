module Spec.K256.Lemmas

open FStar.Mul

open Spec.K256.PointOps

module Euclid = FStar.Math.Euclid
module M = Lib.NatMod
module EC = Spec.EC.Projective

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

let to_aff_point_add_lemma p q = admit()

let to_aff_point_double_lemma p = admit()
