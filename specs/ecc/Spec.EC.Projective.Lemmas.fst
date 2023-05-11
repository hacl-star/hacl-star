module Spec.EC.Projective.Lemmas

open FStar.Mul

module M = Lib.NatMod
module SL = Spec.EC.Lemmas

open Spec.EC.Projective

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val lemma_div_mod_eq_mul_mod (k:curve) (a b c:felem k) : Lemma
  (requires b <> 0)
  (ensures  (fmul k a (finv k b) = c) == (a = fmul k c b))

let lemma_div_mod_eq_mul_mod k a b c =
  prime_lemma ();
  M.lemma_div_mod_eq_mul_mod #prime a b c


val ecdsa_verify_avoid_finv1:
    k:curve{k.order < k.prime /\ k.prime < 2 * k.order}
  -> p:proj_point k{not (is_point_at_inf k p)}
  -> r:nat{0 < r /\ r < k.order} ->
  Lemma (let _X, _Y, _Z = p in
    (fmul k _X (finv k _Z) % k.order = r) ==>
    ((fmul k r _Z = _X) || (r + k.order < k.prime && fmul k (r + k.order) _Z = _X)))

let ecdsa_verify_avoid_finv1 k p r =
  let _X, _Y, _Z = p in
  let x = fmul k _X (finv k _Z) in
  assert (k.order < k.prime /\ k.prime < 2 * k.order);

  if x < k.order then begin
    Math.Lemmas.small_mod x k.order;
    assert ((x % k.order = r) == (x = r));
    assert (r < k.prime /\ _X < k.prime /\ _Z < k.prime /\ _Z <> 0);
    lemma_div_mod_eq_mul_mod k _X _Z r;
    assert ((x % k.order = r) == (fmul k r _Z = _X));
    () end
  else begin
    assert (k.order <= x /\ x < k.prime);
    Math.Lemmas.lemma_mod_sub x k.order 1;
    assert ((x - k.order) % k.order = x % k.order);
    Math.Lemmas.small_mod (x - k.order) k.order;
    assert ((x - k.order) % k.order = x - k.order);
    assert (x % k.order == x - k.order);
    assert ((x % k.order = r) == (x = r + k.order));
    if r + k.order < k.prime then begin
      lemma_div_mod_eq_mul_mod k _X _Z (r + k.order);
      assert ((x % k.order = r) == (r + k.order < k.prime && fmul k (r + k.order) _Z = _X)) end
    else () end


val ecdsa_verify_avoid_finv2:
    k:curve{k.order < k.prime /\ k.prime < 2 * k.order}
  -> p:proj_point k{not (is_point_at_inf k p)}
  -> r:nat{0 < r /\ r < k.order} ->
  Lemma (let _X, _Y, _Z = p in
    ((fmul k r _Z = _X) || (r + k.order < k.prime && fmul k (r + k.order) _Z = _X)) ==>
    (fmul k _X (finv k _Z) % k.order = r))

let ecdsa_verify_avoid_finv2 k p r =
  let _X, _Y, _Z = p in
  let x = fmul k _X (finv k _Z) in
  assert (k.order < k.prime /\ k.prime < 2 * k.order);

  if fmul k r _Z = _X then begin
    lemma_div_mod_eq_mul_mod k _X _Z r;
    Math.Lemmas.small_mod x k.order;
    assert (r = x % k.order) end
  else begin
    if r + k.order < k.prime && fmul k (r + k.order) _Z = _X then begin
      lemma_div_mod_eq_mul_mod k _X _Z (r + k.order);
      assert (r + k.order = x);
      Math.Lemmas.small_mod (x - k.order) k.order;
      Math.Lemmas.lemma_mod_sub x k.order 1;
      assert (r = x % k.order) end
    else () end


let ecdsa_verify_avoid_finv k p r =
  ecdsa_verify_avoid_finv1 k p r;
  ecdsa_verify_avoid_finv2 k p r

//-----------------------------------------

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
  assert (point_at_inf k = (0, 1, 0));
  let zinv = finv k 0 in
  assert (px == fmul k 0 zinv /\ py == fmul k 1 zinv);
  assert (zinv == M.pow_mod #prime 0 (prime - 2));
  M.lemma_pow_mod #prime 0 (prime - 2);
  assert (zinv == M.pow 0 (prime - 2) % prime);
  assert (prime > 2);
  M.lemma_pow_zero (prime - 2);
  assert (zinv == 0);
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
  };
  assert (to_aff_point k (point_negate k p) == aff_point_negate k (to_aff_point k p));
  Spec.EC.Lemmas.aff_point_negate_inv_lemma k (to_aff_point k p);
  assert (point_inv k (point_negate k p))


let to_aff_point_add_lemma_a3 k p q = admit()

let to_aff_point_double_lemma_a3 k p = admit()


let to_aff_point_add_lemma_a0 k p q = admit()

let to_aff_point_double_lemma_a0 k p = admit()
