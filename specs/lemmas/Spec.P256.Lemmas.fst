module Spec.P256.Lemmas

open FStar.Mul
open Spec.P256.PointOps

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

let prime_lemma () = admit()

let aff_point_at_inf_lemma p = admit()

let aff_point_add_assoc_lemma p q s = admit ()

let aff_point_add_comm_lemma p q = admit()

let to_aff_point_at_infinity_lemma () = admit()

let to_aff_point_add_lemma p q = admit()

let to_aff_point_double_lemma p = admit()
