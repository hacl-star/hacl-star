module Spec.K256.Lemmas

open FStar.Mul

open Spec.K256.PointOps

module Euclid = FStar.Math.Euclid
module M = Lib.NatMod
module EC = Spec.EC.Projective

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

let aff_point_negate_lemma p =
  let p_neg = aff_point_negate p in
  let px, py = p in
  let qx, qy = p_neg in
  assert (qx = px /\ qy = (-py) % prime);
  assert (EC.aff_point_add k256 p_neg p == EC.aff_point_at_inf k256)


let to_aff_point_at_infinity_lemma () =
  let px, py = EC.to_aff_point k256 (EC.point_at_inf k256) in
  assert (px == 0 /% 0 /\ py == 1 /% 0);
  assert (px == 0 *% M.pow_mod #prime 0 (prime - 2));
  M.lemma_pow_mod #prime 0 (prime - 2);
  assert (px == 0 *% (M.pow 0 (prime - 2) % prime));
  M.lemma_pow_zero (prime - 2);
  assert (px == 0 /\ py == 0)

let to_aff_point_add_lemma p q = admit()

let to_aff_point_double_lemma p = admit()

let to_aff_point_negate_lemma p =
  let px, py, pz = p in
  let qx, qy = EC.to_aff_point k256 (point_negate p) in
  assert (qx == px /% pz /\ qy == (- py) % prime /% pz);
  let ax, ay = aff_point_negate (EC.to_aff_point k256 p) in
  assert (ax == px /% pz /\ ay == (- py /% pz) % prime);
  let pz_inv = M.pow_mod #prime pz (prime - 2) in

  calc (==) { // (-py) % prime /% pz;
    ((- py) % prime * pz_inv) % prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (- py) pz_inv prime }
    (- py * pz_inv) % prime;
    (==) { Math.Lemmas.neg_mul_left py pz_inv }
    (- (py * pz_inv)) % prime;
    (==) { Math.Lemmas.lemma_mod_sub_distr 0 (py * pz_inv) prime }
    (- (py * pz_inv) % prime) % prime; // (- py /% pz) % prime;
  }

//----------------------------------

val lemma_div_mod_eq_mul_mod (a b c:felem) : Lemma
  (requires b <> 0)
  (ensures  (a *% EC.finv k256 b = c) == (a = c *% b))

let lemma_div_mod_eq_mul_mod a b c =
  prime_lemma ();
  M.lemma_div_mod_eq_mul_mod #prime a b c


val ecdsa_verify_avoid_finv1:
  p:EC.proj_point k256{not (EC.is_point_at_inf k256 p)} -> r:nat{0 < r /\ r < q} ->
  Lemma (let _X, _Y, _Z = p in
    (_X /% _Z % q = r) ==> ((r *% _Z = _X) || (r + q < prime && (r + q) *% _Z = _X)))

let ecdsa_verify_avoid_finv1 p r =
  let _X, _Y, _Z = p in
  let x = _X /% _Z in
  assert_norm (prime < 2 * q);
  assert_norm (q < prime);

  if x < q then begin
    Math.Lemmas.small_mod x q;
    assert ((x % q = r) == (x = r));
    assert (r < prime /\ _X < prime /\ _Z < prime /\ _Z <> 0);
    lemma_div_mod_eq_mul_mod _X _Z r;
    assert ((x % q = r) == (r *% _Z = _X));
    () end
  else begin
    Math.Lemmas.lemma_mod_sub x q (-1);
    Math.Lemmas.small_mod (x - q) q;
    assert (x % q == x - q);
    assert ((x % q = r) == (x = r + q));
    if r + q < prime then begin
      lemma_div_mod_eq_mul_mod _X _Z (r + q);
      assert ((x % q = r) == (r + q < prime && (r + q) *% _Z = _X)) end
    else () end


val ecdsa_verify_avoid_finv2:
  p:EC.proj_point k256{not (EC.is_point_at_inf k256 p)} -> r:nat{0 < r /\ r < q} ->
  Lemma (let _X, _Y, _Z = p in
    ((r *% _Z = _X) || (r + q < prime && (r + q) *% _Z = _X)) ==> (_X /% _Z % q = r))

let ecdsa_verify_avoid_finv2 p r =
  let _X, _Y, _Z = p in
  let x = _X /% _Z in
  assert_norm (prime < 2 * q);
  assert_norm (q < prime);

  if r *% _Z = _X then begin
    lemma_div_mod_eq_mul_mod _X _Z r;
    Math.Lemmas.small_mod x q;
    assert (r = x % q) end
  else begin
    if r + q < prime && (r + q) *% _Z = _X then begin
      lemma_div_mod_eq_mul_mod _X _Z (r + q);
      assert (r + q = x);
      Math.Lemmas.small_mod (x - q) q;
      Math.Lemmas.lemma_mod_sub x q (-1);
      assert (r = x % q) end
    else () end


let ecdsa_verify_avoid_finv p r =
  ecdsa_verify_avoid_finv1 p r;
  ecdsa_verify_avoid_finv2 p r
