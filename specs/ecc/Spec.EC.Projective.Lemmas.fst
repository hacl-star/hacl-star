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


let to_aff_point_at_infinity_lemma k =
  let px, py = to_aff_point k (point_at_inf k) in
  assert (px == fmul k 0 (finv k 0) /\ py == fmul k 1 (finv k 0));
  assert (px == fmul k 0 (M.pow_mod #prime 0 (prime - 2)));
  M.lemma_pow_mod #prime 0 (prime - 2);
  assert (px == fmul k 0 (M.pow 0 (prime - 2) % prime));
  M.lemma_pow_zero (prime - 2);
  assert (px == 0 /\ py == 0)


let to_aff_point_negate_lemma k p =
  let px, py, pz = p in
  let qx, qy = to_aff_point k (point_negate k p) in
  assert (qx == fmul k px (finv k pz) /\ qy == fmul k ((- py) % prime) (finv k pz));
  let ax, ay = aff_point_negate k (to_aff_point k p) in
  assert (ax == fmul k px (finv k pz) /\ ay == (- (fmul k py (finv k pz))) % prime);
  let pz_inv = M.pow_mod #prime pz (prime - 2) in

  calc (==) { // (-py) % prime /% pz;
    ((- py) % k.prime * pz_inv) % k.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (- py) pz_inv k.prime }
    ((- py) * pz_inv) % k.prime;
    (==) { Math.Lemmas.neg_mul_left py pz_inv }
    (- (py * pz_inv)) % k.prime;
    (==) { Math.Lemmas.lemma_mod_sub_distr 0 (py * pz_inv) k.prime }
    (- (py * pz_inv) % k.prime) % k.prime; // (- py /% pz) % prime;
  }
