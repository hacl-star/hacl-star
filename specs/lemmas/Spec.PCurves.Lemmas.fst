module Spec.PCurves.Lemmas

open FStar.Mul
open Spec.PCurves.PointOps

module M = Lib.NatMod

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

let prime_lemma c = admit()

let lemma_exp_prime p x = admit()
let lemma_exp_inv_prime p x y = admit()

let lemma_aff_is_point_at_inf #c p =
  prime_lemma c;
  let (px, py, pz) = p in
  M.lemma_div_mod_prime_is_zero #prime px pz;
  M.lemma_div_mod_prime_is_zero #prime py pz


let aff_point_at_inf_lemma p = admit()

let aff_point_add_assoc_lemma p q s = admit ()

let aff_point_add_comm_lemma p q = admit()

let to_aff_point_at_infinity_lemma #c = admit()

let to_aff_point_add_lemma p q = admit()

let to_aff_point_double_lemma p = admit()
