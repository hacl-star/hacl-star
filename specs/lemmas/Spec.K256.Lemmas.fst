module Spec.K256.Lemmas

open FStar.Mul

open Spec.K256.PointOps

module Euclid = FStar.Math.Euclid
module M = Lib.NatMod

open FStar.Algebra.CommMonoid
open FStar.Tactics.CanonCommSemiring
open FStar.Tactics

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

assume val prime_lemma: unit -> Lemma (Euclid.is_prime prime)

let lemma_aff_is_point_at_inf p =
  prime_lemma ();
  let (px, py, pz) = p in
  M.lemma_div_mod_prime_is_zero #prime px pz;
  M.lemma_div_mod_prime_is_zero #prime py pz


let lemma_proj_aff_id p =
  let (px, py) = p in
  let (pX, pY, pZ) = to_proj_point p in
  assert (pX = px /\ pY = pY /\ pZ = one);
  let (rx, ry) = to_aff_point (pX, pY, pZ) in
  assert (rx = (pX /% pZ) /\ ry = (pY /% pZ));
  M.lemma_div_mod_prime_one #prime pX;
  M.lemma_div_mod_prime_one #prime pY;
  assert (rx = pX /\ ry = pY)

/// Field facts

[@canon_attr]
noextract
let felem_add_cm : cm felem =
  CM zero ( +% ) (M.lemma_add_mod_one #prime) (M.lemma_add_mod_assoc #prime) (M.lemma_add_mod_comm #prime)

[@canon_attr]
noextract
let felem_mul_cm : cm felem =
  CM one ( *% ) (M.lemma_mul_mod_one #prime) (M.lemma_mul_mod_assoc #prime) (M.lemma_mul_mod_comm #prime)

val fmul_zero_l: mult_zero_l_lemma felem felem_add_cm felem_mul_cm
let fmul_zero_l a = assert_norm (forall x. zero *% x == zero)

let ( ~% ) (a:felem) : felem = (-a) % prime

val fadd_opp (a:felem) : Lemma (a +% ~%a == zero)
let fadd_opp a =
  FStar.Math.Lemmas.lemma_mod_add_distr a (-a) prime;
  FStar.Math.Lemmas.small_mod 0 prime

[@canon_attr]
noextract
let felem_cr : cr felem =
  CR felem_add_cm felem_mul_cm ( ~% ) fadd_opp (M.lemma_mod_distributivity_add_right #prime) fmul_zero_l

noextract
let k256_semiring () : Tac unit = canon_semiring felem_cr; trefl()

val finv_zero: unit -> Lemma (finv 0 == 0)
let finv_zero () =
  M.lemma_pow_mod #prime 0 (prime - 2);
  M.lemma_pow_zero (prime - 2)

val finv_one: unit -> Lemma (finv 1 == 1)
let finv_one () =
  M.lemma_pow_mod #prime 1 (prime - 2);
  M.lemma_pow_one (prime - 2)

val fmul_finv: z:felem -> Lemma (requires z <> 0) (ensures z *% finv z == 1)
let fmul_finv z =
  prime_lemma ();
  M.lemma_div_mod_prime #prime z

val fmul_one: a:felem -> Lemma (a *% one == a)
let fmul_one a = M.lemma_mul_mod_one #prime a

val fmul_eq_zero: a:felem -> b:felem -> Lemma (a *% b == 0 <==> (a == 0 \/ b == 0))
let fmul_eq_zero a b =
  prime_lemma ();
  M.lemma_mul_mod_prime_zero #prime a b


/// Valid points

let aff_lhs (x y w:felem) : felem = (y *% w) *% (y *% w)
let aff_rhs (x y w:felem) : felem = (x *% w) *% (x *% w) *% (x *% w) +% b
let proj_lhs (x y z:felem) : felem = y *% y *% z
let proj_rhs (x y z:felem) : felem = x *% x *% x +% b *% z *% z *% z

val proj_of_aff (x y z w:felem) : Lemma
  (requires z *% w == 1)
  (ensures  proj_lhs x y z == aff_lhs x y w *% (z *% z *% z) /\
            proj_rhs x y z == aff_rhs x y w *% (z *% z *% z))
let proj_of_aff x y z w =
  let zw = z *% w in
  assert (aff_lhs x y w *% (z *% z *% z) == proj_lhs x y z *% (zw *% zw))
    by (norm [delta_only [`%aff_lhs; `%proj_lhs]]; k256_semiring ());
  assert (aff_rhs x y w *% (z *% z *% z) ==
          x *% x *% x *% (zw *% zw *% zw) +% b *% z *% z *% z)
    by (norm [delta_only [`%aff_rhs]]; k256_semiring ());
  fmul_one one;
  fmul_one (proj_lhs x y z);
  fmul_one (x *% x *% x)

val aff_of_proj (x y z w:felem) : Lemma
  (requires z *% w == 1)
  (ensures  aff_lhs x y w == proj_lhs x y z *% (w *% w *% w) /\
            aff_rhs x y w == proj_rhs x y z *% (w *% w *% w))
let aff_of_proj x y z w =
  let zw = z *% w in
  assert (proj_lhs x y z *% (w *% w *% w) == aff_lhs x y w *% zw)
    by (norm [delta_only [`%aff_lhs; `%proj_lhs]]; k256_semiring ());
  assert (proj_rhs x y z *% (w *% w *% w) ==
          (x *% w) *% (x *% w) *% (x *% w) +% b *% (zw *% zw *% zw))
    by (norm [delta_only [`%proj_rhs]]; k256_semiring ());
  fmul_one one;
  fmul_one (one *% one);
  fmul_one (aff_lhs x y w);
  fmul_one b

let point_inv_lemma p =
  let (x, y, z) = p in
  if z = 0 then begin
    assert (proj_lhs x y z == 0);
    assert (proj_rhs x y z == x *% x *% x);
    fmul_eq_zero x x;
    fmul_eq_zero (x *% x) x;
    assert (is_on_proj_curve p <==> x = 0) end
  else begin
    let w = finv z in
    fmul_finv z;
    proj_of_aff x y z w;
    aff_of_proj x y z w;
    assert (to_aff_point p == (x *% w, y *% w));
    assert (is_on_curve (to_aff_point p) <==> aff_lhs x y w == aff_rhs x y w);
    assert (is_on_proj_curve p <==> proj_lhs x y z == proj_rhs x y z) end

let aff_point_at_inf_inv () = ()

let point_at_inf_inv () = assert_norm (point_inv point_at_inf)

let g_inv () =
  finv_one ();
  fmul_one g_x;
  fmul_one g_y;
  assert (to_aff_point g == (g_x, g_y));
  assert_norm (is_on_curve (g_x, g_y));
  assert_norm (point_inv g)

let to_aff_point_inv p =
  let (x, y, z) = p in
  point_inv_lemma p;
  if z = 0 then finv_zero () else ()

let to_proj_point_inv p =
  let (x, y) = p in
  finv_one ();
  fmul_one x;
  fmul_one y;
  point_inv_lemma (to_proj_point p)

let load_point_inv b =
  match aff_point_load b with
  | Some p -> to_proj_point_inv p
  | None -> ()

let aff_point_negate_inv p =
  let (x, y) = p in
  assert (~% y *% ~% y == y *% y) by (k256_semiring ());
  if y = 0 then () else ()

let point_negate_inv p =
  let (x, y, z) = p in
  assert (~% y *% ~% y *% z == y *% y *% z) by (k256_semiring ());
  assert (y <> 0 ==> ~% y <> 0)


let aff_point_mul_x_inv c p =
  let (x, y) = p in
  assert ((c *% x) *% (c *% x) *% (c *% x) == (c *% c *% c) *% (x *% x *% x)) by (k256_semiring ());
  assert (one *% (x *% x *% x) == (x *% x *% x) *% one) by (k256_semiring ());
  fmul_one (x *% x *% x);
  assert (c *% 0 == 0)

let point_mul_x_inv c p =
  let (x, y, z) = p in
  assert ((c *% x) *% (c *% x) *% (c *% x) == (c *% c *% c) *% (x *% x *% x)) by (k256_semiring ());
  assert (one *% (x *% x *% x) == (x *% x *% x) *% one) by (k256_semiring ());
  fmul_one (x *% x *% x);
  fmul_eq_zero c x;
  assert (c <> 0)


/// Affine group law

let aff_point_at_inf_lemma p = ()

let aff_point_add_inv_lemma p q = admit ()

let aff_point_add_assoc_lemma p q s = admit()

val fsub_opp: x:felem -> y:felem -> Lemma (x -% y == x +% ~% y)
let fsub_opp x y = FStar.Math.Lemmas.lemma_mod_add_distr x (-y) prime

val fsub_swap: x:felem -> y:felem -> Lemma (y -% x == ~% (x -% y))
let fsub_swap x y = FStar.Math.Lemmas.lemma_mod_sub_distr 0 (x - y) prime

val finv_opp: d:felem -> Lemma (requires d <> 0) (ensures finv (~% d) == ~% (finv d))
let finv_opp d =
  let d' = ~% d in
  let w = finv d in
  let w' = finv d' in
  assert (d' = prime - d);
  fmul_finv d;
  fmul_finv d';
  assert (d' *% ~% w == d *% w) by (k256_semiring ());
  assert (w' *% (d' *% ~% w) == (d' *% w') *% ~% w) by (k256_semiring ());
  fmul_one w';
  assert (one *% ~% w == ~% w *% one) by (k256_semiring ());
  fmul_one (~% w)

val fadd_cancel: a:felem -> b:felem -> c:felem -> Lemma
  (requires a +% c == b +% c) (ensures a == b)
let fadd_cancel a b c =
  assert (a +% c +% ~% c == a +% (c +% ~% c)) by (k256_semiring ());
  assert (b +% c +% ~% c == b +% (c +% ~% c)) by (k256_semiring ());
  fadd_opp c;
  M.lemma_add_mod_one #prime a;
  M.lemma_add_mod_one #prime b

// Unconditional: only needs `finv (-d) = - finv d` and `d * finv d = 1` for `d <> 0`.
let aff_point_add_comm_lemma p q =
  let (px, py) = p in let (qx, qy) = q in
  if is_aff_point_at_inf p || is_aff_point_at_inf q || p = q || qx = px then ()
  else begin
    let d = qx -% px in
    let u = qy -% py in
    let w = finv d in
    assert (d <> 0);
    fsub_swap qx px;
    fsub_swap qy py;
    finv_opp d;
    let l = u *% w in
    assert (~% u *% ~% w == u *% w) by (k256_semiring ());
    assert ((py -% qy) /% (px -% qx) == l);
    let rx = l *% l -% px -% qx in
    fsub_opp (l *% l) px; fsub_opp (l *% l +% ~% px) qx;
    fsub_opp (l *% l) qx; fsub_opp (l *% l +% ~% qx) px;
    assert (l *% l +% ~% px +% ~% qx == l *% l +% ~% qx +% ~% px) by (k256_semiring ());
    assert (l *% l -% qx -% px == rx);
    fsub_opp px rx; fsub_opp qx rx;
    fsub_opp (l *% (px +% ~% rx)) py; fsub_opp (l *% (qx +% ~% rx)) qy;
    fsub_opp qx px; fsub_opp qy py;
    fmul_finv d;
    // l (px - rx) - py + u (d w)  ==  l (qx - rx) - qy + u,  and  d w = 1
    assert ((qy +% ~% py) *% w *% (px +% ~% rx) +% ~% py +%
            (qy +% ~% py) *% ((qx +% ~% px) *% w) ==
            (qy +% ~% py) *% w *% (qx +% ~% rx) +% ~% qy +% (qy +% ~% py))
      by (k256_semiring ());
    fmul_one u;
    fadd_cancel (l *% (px -% rx) -% py) (l *% (qx -% rx) -% qy) u
  end

let aff_point_negate_lemma p =
  let p_neg = aff_point_negate p in
  let px, py = p in
  let qx, qy = p_neg in
  assert (qx = px /\ qy = (-py) % prime);
  assert (aff_point_add p_neg p == aff_point_at_inf)


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
    == { Math.Lemmas.lemma_mod_mul_distr_l (- py) pz_inv prime }
    (- py * pz_inv) % prime;
    == { Math.Lemmas.neg_mul_left py pz_inv }
    (- (py * pz_inv)) % prime;
    == { Math.Lemmas.lemma_mod_sub_distr 0 (py * pz_inv) prime }
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
