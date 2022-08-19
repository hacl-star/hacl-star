module Spec.K256.Lemmas

open FStar.Mul

open Spec.K256.PointOps

module Euclid = FStar.Math.Euclid
module M = Lib.NatMod

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

assume val prime_lemma: unit -> Lemma (Euclid.is_prime prime)

let aff_point_at_inf_lemma p = admit()

let aff_point_add_assoc_lemma p q s = admit()

let aff_point_add_comm_lemma p q = admit()

let aff_point_negate_lemma p = admit()

let to_aff_point_at_infinity_lemma () =
  let px, py = to_aff_point point_at_inf in
  assert (px == zero /% zero /\ py == one /% zero);
  assert (px == zero *% M.pow_mod #prime zero (prime - 2));
  M.lemma_pow_mod #prime zero (prime - 2);
  assert (px == zero *% (M.pow zero (prime - 2) % prime));
  M.lemma_pow_zero (prime - 2);
  assert (px == zero /\ py == zero)

let to_aff_point_add_lemma p q = admit()

let to_aff_point_double_lemma p = admit()

let to_aff_point_negate_lemma p =
  let px, py, pz = p in
  let qx, qy = to_aff_point (point_negate p) in
  assert (qx == px /% pz /\ qy == (- py) % prime /% pz);
  let ax, ay = aff_point_negate (to_aff_point p) in
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
  (ensures  (a *% finv b = c) == (a = c *% b))

let lemma_div_mod_eq_mul_mod a b c =
  prime_lemma ();
  M.lemma_div_mod_eq_mul_mod #prime a b c


val ecdsa_verify_avoid_finv1:
  p:proj_point{not (is_proj_point_at_inf p)} -> r:nat{0 < r /\ r < q} ->
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
  p:proj_point{not (is_proj_point_at_inf p)} -> r:nat{0 < r /\ r < q} ->
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
