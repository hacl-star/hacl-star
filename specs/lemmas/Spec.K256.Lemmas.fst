module Spec.K256.Lemmas

open FStar.Mul

open Spec.K256.PointOps

module Euclid = FStar.Math.Euclid
module M = Lib.NatMod

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

assume val prime_lemma: unit -> Lemma (Euclid.is_prime prime)

val mul_zero_lemma: n:pos{Euclid.is_prime n} -> x:int -> y:int ->
  Lemma (x * y % n == 0 <==> (x % n == 0 \/ y % n == 0))

let mul_zero_lemma n x y =
  assert (0 % n = 0);
  if x % n = 0 then
    Math.Lemmas.lemma_mod_mul_distr_l x y n
  else
    if y % n = 0 then
      Math.Lemmas.lemma_mod_mul_distr_r x y n
    else
      if x * y % n = 0 then
        Math.Fermat.mod_mult_congr n x 0 y
      else ()


val lemma_aff_is_point_at_inf1: p:proj_point -> Lemma
  (requires is_proj_point_at_inf p)
  (ensures  is_aff_point_at_inf (to_aff_point p))

let lemma_aff_is_point_at_inf1 p =
  let (px, py, pz) = p in
  let zinv = finv pz in
  Lib.NatMod.lemma_pow_mod #prime pz (prime - 2);
  Lib.NatMod.lemma_pow_zero (prime - 2);
  assert (zinv = 0)


val finv_zero_is_zero: a:felem -> n:pos -> Lemma
  (requires M.pow a n % prime = 0)
  (ensures  a = 0)

let rec finv_zero_is_zero a n =
  if n = 1 then M.lemma_pow1 a
  else begin
    let r1 = M.pow a (n - 1) % prime in
    M.lemma_pow_unfold a n;
    assert (a * M.pow a (n - 1) % prime = 0);
    Math.Lemmas.lemma_mod_mul_distr_r a (M.pow a (n - 1)) prime;
    prime_lemma ();
    mul_zero_lemma prime a r1;
    assert (a = 0 \/ r1 = 0);
    if a = 0 then () else finv_zero_is_zero a (n - 1) end


val lemma_aff_is_point_at_inf2: p:proj_point -> Lemma
  (requires is_aff_point_at_inf (to_aff_point p))
  (ensures  (let px, py, pz = p in pz = 0 \/ (px = 0 /\ py = 0)))

let lemma_aff_is_point_at_inf2 p =
  let (px, py, pz) = p in
  let zinv = finv pz in
  let x = fmul px zinv in
  let y = fmul py zinv in
  assert (x == 0 /\ y == 0);
  prime_lemma ();
  mul_zero_lemma prime px zinv;
  mul_zero_lemma prime py zinv;

  if zinv = 0 then begin
    Lib.NatMod.lemma_pow_mod #prime pz (prime - 2);
    finv_zero_is_zero pz (prime - 2);
    assert (pz = 0) end


let lemma_aff_is_point_at_inf p =
  Classical.move_requires lemma_aff_is_point_at_inf1 p;
  Classical.move_requires lemma_aff_is_point_at_inf2 p


let lemma_proj_aff_id p =
  let (px, py) = p in
  let (pX, pY, pZ) = to_proj_point p in
  assert (pX = px /\ pY = pY /\ pZ = one);
  let (rx, ry) = to_aff_point (pX, pY, pZ) in
  assert (rx = (pX /% pZ) /\ ry = (pY /% pZ));
  M.lemma_div_mod_prime_one #prime pX;
  M.lemma_div_mod_prime_one #prime pY;
  assert (rx = pX /\ ry = pY)

let aff_point_at_inf_lemma p = admit()

let aff_point_add_assoc_lemma p q s = admit()

let aff_point_add_comm_lemma p q = admit()

let to_aff_point_at_infinity_lemma () = admit()

let to_aff_point_add_lemma p q = admit()

let to_aff_point_double_lemma p = admit()


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
