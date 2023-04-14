module Spec.P256.Lemmas

open FStar.Mul
open Spec.P256.PointOps

module M = Lib.NatMod

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

let prime_lemma () = admit()

let lemma_aff_is_point_at_inf p =
  prime_lemma ();
  let (px, py, pz) = p in
  M.lemma_div_mod_prime_is_zero #prime px pz;
  M.lemma_div_mod_prime_is_zero #prime py pz


let aff_point_at_inf_lemma p = admit()

let aff_point_add_assoc_lemma p q s = admit ()

let aff_point_add_comm_lemma p q = admit()

let to_aff_point_at_infinity_lemma () = admit()

let to_aff_point_add_lemma p q = admit()

let to_aff_point_double_lemma p = admit()
