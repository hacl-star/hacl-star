module Spec.EC.Projective.Lemmas

open FStar.Mul

module M = Lib.NatMod

open Spec.EC.Projective

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let lemma_aff_is_point_at_inf k p =
  k.prime_lemma ();
  let (px, py, pz) = p in
  M.lemma_div_mod_prime_is_zero #prime px pz;
  M.lemma_div_mod_prime_is_zero #prime py pz


let lemma_proj_aff_id k p =
  let (px, py) = p in
  let (pX, pY, pZ) = to_proj_point k p in
  assert (pX = px /\ pY = pY /\ pZ = 1);
  let (rx, ry) = to_aff_point k (pX, pY, pZ) in
  assert (rx = fmul k pX (finv k pZ) /\ ry = fmul k pY (finv k pZ));
  M.lemma_div_mod_prime_one #prime pX;
  M.lemma_div_mod_prime_one #prime pY;
  assert (rx = pX /\ ry = pY)
