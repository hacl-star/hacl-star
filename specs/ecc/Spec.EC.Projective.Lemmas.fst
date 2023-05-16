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

val lemma_abc_is_zero (n:pos) (a b c:int) : Lemma
  (requires c = 0)
  (ensures  (a * b % n) * c % n = 0)

let lemma_abc_is_zero n a b c =
  calc (==) {
    (a * b % n) * c % n;
    (==) { }
    (a * b % n) * 0 % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a * b) 0 n }
    (a * b) * 0 % n;
    (==) { Math.Lemmas.paren_mul_right a b 0; Math.Lemmas.mul_zero_right_is_zero b }
    a * 0 % n;
    (==) { Math.Lemmas.mul_zero_right_is_zero a; Math.Lemmas.small_mod 0 n }
    0;
   };
  assert ((a * b % n) * c % n = 0)


let point_inv_is_point_at_inf k p =
  let ( +% ) = fadd k in
  let ( *% ) = fmul k in
  let (x, y, z) = p in

  assert (point_inv k p);
  assert (z = 0);
  lemma_abc_is_zero k.prime y y z;
  assert (y *% y *% z = 0);

  lemma_abc_is_zero k.prime z z z;
  assert (z *% z *% z = 0);
  assert (k.coeff_b *% (z *% z *% z) = 0);

  lemma_abc_is_zero k.prime k.coeff_a x (z *% z);
  assert (k.coeff_a *% x *% (z *% z) = 0);
  assert (x *% x *% x +% k.coeff_a *% x *% (z *% z) +% k.coeff_b *% (z *% z *% z) ==
    x *% x *% x +% k.coeff_a *% x *% (z *% z) +% 0);
  Math.Lemmas.small_mod (x *% x *% x +% k.coeff_a *% x *% (z *% z)) k.prime;
  assert (x *% x *% x +% k.coeff_a *% x *% (z *% z) +% k.coeff_b *% (z *% z *% z) ==
    x *% x *% x +% 0);
  Math.Lemmas.small_mod (x *% x *% x) k.prime;
  assert (0 == x *% x *% x);

  k.prime_lemma ();
  Lib.NatMod.lemma_mul_mod_prime_zero #k.prime (x *% x) x;
  assert ((x *% x) % k.prime = 0 \/ x % k.prime = 0);
  Math.Lemmas.small_mod x k.prime;
  Math.Lemmas.small_mod (x *% x) k.prime;
  Lib.NatMod.lemma_mul_mod_prime_zero #k.prime x x;
  assert (x = 0)


let lemma_is_point_at_inf k p =
  let x, y, z = p in
  let px, py = to_aff_point k p in
  let zinv = finv k 0 in
  assert (px == fmul k x zinv /\ py == fmul k y zinv);
  assert (zinv == M.pow_mod #prime 0 (prime - 2));
  M.lemma_pow_mod #prime 0 (prime - 2);
  assert (zinv == M.pow 0 (prime - 2) % prime);
  assert (prime > 2);
  M.lemma_pow_zero (prime - 2);
  Math.Lemmas.small_mod 0 k.prime;
  assert (zinv == 0);
  assert (px == 0 /\ py == 0)


val point_inv_ec_lemma1: k:curve -> p:proj_point k -> Lemma
  (requires point_inv k p /\ not (is_point_at_inf k p))
  (ensures  is_on_curve k (to_aff_point k p))

let point_inv_ec_lemma1 k p =
  let ( +% ) = fadd k in
  let ( *% ) = fmul k in
  let ( /% ) a b = fmul k a (finv k b) in
  let (x, y, z) = p in
  assert (y *% y *% z = x *% x *% x +% k.coeff_a *% x *% (z *% z) +% k.coeff_b *% (z *% z *% z));
  let px = x /% z in
  let py = y /% z in
  assert (z <> 0);
  assume (py *% py = px *% px *% px +% k.coeff_a *% px +% k.coeff_b);
  assert (is_on_curve k (px, py))


val point_inv_ec_lemma2: k:curve -> p:proj_point k -> Lemma
  (requires is_on_curve k (to_aff_point k p) /\ not (is_point_at_inf k p))
  (ensures  point_inv k p)

let point_inv_ec_lemma2 k p =
  let ( +% ) = fadd k in
  let ( *% ) = fmul k in
  let ( /% ) a b = fmul k a (finv k b) in
  let (x, y, z) = p in
  let px = x /% z in
  let py = y /% z in
  assert (py *% py = px *% px *% px +% k.coeff_a *% px +% k.coeff_b);
  assert (z <> 0);
  assume (y *% y *% z = x *% x *% x +% k.coeff_a *% x *% (z *% z) +% k.coeff_b *% (z *% z *% z))


let point_inv_ec_lemma k p =
  Classical.move_requires (point_inv_ec_lemma1 k) p;
  Classical.move_requires (point_inv_ec_lemma2 k) p


let point_inv_lemma k p =
  if is_point_at_inf k p then ()
  else point_inv_ec_lemma k p


let lemma_aff_is_point_at_inf k p =
  k.prime_lemma ();
  let (px, py, pz) = p in
  M.lemma_div_mod_prime_is_zero #prime px pz;
  M.lemma_div_mod_prime_is_zero #prime py pz


val lemma_aff_is_point_at_inf_to_aff: k:curve -> p:proj_point k{point_inv_to_aff k p} ->
  Lemma (let px, py, pz = p in is_aff_point_at_inf k (to_aff_point k p) == (pz = 0))

let lemma_aff_is_point_at_inf_to_aff k p =
  lemma_aff_is_point_at_inf k p


let lemma_aff_is_point_at_inf_c k p =
  point_inv_lemma k p;
  lemma_aff_is_point_at_inf_to_aff k p


let lemma_proj_aff_id k p =
  let (px, py) = p in
  let (pX, pY, pZ) = to_proj_point k p in
  let (rx, ry) = to_aff_point k (pX, pY, pZ) in

  if is_aff_point_at_inf k p then
    lemma_is_point_at_inf k (point_at_inf k)
  else begin
    assert (pX = px /\ pY = pY /\ pZ = 1);
    assert (rx = fmul k pX (finv k pZ) /\ ry = fmul k pY (finv k pZ));
    M.lemma_div_mod_prime_one #prime pX;
    M.lemma_div_mod_prime_one #prime pY;
    assert (rx = pX /\ ry = pY) end

//----------------

let lemma_point_at_inf_c k =
  let ( +% ) = fadd k in
  let ( *% ) = fmul k in
  let (x, y, z) = point_at_inf k in
  assert (x = 0 && z = 0 && y = 1);
  lemma_abc_is_zero k.prime y y z;
  assert (y *% y *% z = 0);
  lemma_abc_is_zero k.prime x x x;
  assert (x *% x *% x = 0);
  lemma_abc_is_zero k.prime k.coeff_a x (z *% z);
  lemma_abc_is_zero k.prime z z z;
  assert (y *% y *% z =
    x *% x *% x +% k.coeff_a *% x *% (z *% z) +% k.coeff_b *% (z *% z *% z))


let lemma_to_aff_point_c k p =
  if is_point_at_inf k p then
    lemma_is_point_at_inf k p
  else point_inv_ec_lemma k p


let lemma_to_proj_point_c k p =
  let px, py = p in
  if is_aff_point_at_inf k p then begin
    assert (to_proj_point k p = point_at_inf k);
    lemma_point_at_inf_c k end
  else begin
    k.prime_lemma ();
    Lib.NatMod.lemma_div_mod_prime_one #k.prime px;
    Lib.NatMod.lemma_div_mod_prime_one #k.prime py;
    point_inv_ec_lemma k (to_proj_point k p) end

//-----------------

let to_aff_point_at_infinity_lemma k =
  lemma_is_point_at_inf k (point_at_inf k)


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

  if is_point_at_inf k p then begin
    assert (pz = 0);
    assert (point_inv k (point_negate k p)) end
  else begin
    point_inv_ec_lemma k p;
    Spec.EC.Lemmas.aff_point_negate_on_curve_lemma k (to_aff_point k p);
    assert (is_on_curve k (aff_point_negate k (to_aff_point k p)));
    assert (is_on_curve k (to_aff_point k (point_negate k p)));
    point_inv_ec_lemma k (point_negate k p);
    assert (point_inv k (point_negate k p)) end


let to_aff_point_add_lemma_a3 k p q = admit()

let to_aff_point_double_lemma_a3 k p = admit()


let to_aff_point_add_lemma_a0 k p q = admit()

let to_aff_point_double_lemma_a0 k p = admit()
