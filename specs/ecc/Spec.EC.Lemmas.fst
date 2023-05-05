module Spec.EC.Lemmas

open FStar.Mul
open Spec.EC

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

let aff_point_at_inf_lemma (k:curve) (p:aff_point k) = admit()

let aff_point_add_assoc_lemma (k:curve) (p q s:aff_point k) = admit()

let aff_point_add_comm_lemma (k:curve) (p q:aff_point k) = admit()
