module Hacl.Spec.K256.GLV

open FStar.Mul

module M = Lib.NatMod
module S = Spec.K256
module LS = Spec.K256.Lemmas
module GL = Hacl.Spec.K256.ECSM.Lemmas

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

// For more comments see https://github.com/bitcoin-core/secp256k1/blob/master/src/scalar_impl.h

(**
 Fast computation of [lambda]P as (beta * x, y) in affine coordinates
*)

let lambda : S.qelem = 0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72

val lambda_is_primitive_cube_root_unity: unit -> Lemma
  (lambda <> 1 /\
  S.(lambda *^ lambda *^ lambda = 1) /\
  S.(lambda *^ lambda +^ lambda +^ 1 = 0))

let lambda_is_primitive_cube_root_unity () =
  assert (lambda <> 1);
  assert (S.(lambda *^ lambda *^ lambda = 1));
  assert (S.(lambda *^ lambda +^ lambda +^ 1 = 0))


let beta : S.felem = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee

val beta_is_primitive_cube_root_unity: unit -> Lemma
  (beta <> 1 /\
   S.(beta *% beta *% beta = 1) /\
   S.(beta *% beta +% beta +% 1 = 0))

let beta_is_primitive_cube_root_unity () =
  assert (beta <> 1);
  assert (S.(beta *% beta *% beta = 1));
  assert (S.(beta *% beta +% beta +% 1 = 0))


// [a]P in affine coordinates
let aff_point_mul = S.aff_point_mul

// [a]G in affine coordinates
let aff_point_mul_g (a:nat) : S.aff_point =
  aff_point_mul a S.(g_x, g_y)

// fast computation of [lambda]P in affine coordinates
let aff_point_mul_lambda (p:S.aff_point) : S.aff_point =
  let (px, py) = p in (S.(beta *% px), py)

// fast computation of [lambda]G in affine coordinates
let aff_point_mul_g_lambda () : S.aff_point =
  (S.(beta *% S.g_x), S.g_y)


assume
val lemma_glv_aff : p:S.aff_point -> Lemma (aff_point_mul lambda p = aff_point_mul_lambda p)

val lemma_glv_g_aff : unit -> Lemma (aff_point_mul_g lambda = aff_point_mul_g_lambda ())
let lemma_glv_g_aff () = lemma_glv_aff S.(g_x, g_y)
// or, we can prove it by assert_norm


(**
 Fast computation of [lambda]P as (beta * x, y) in projective coordinates
*)

// fast computation of [lambda]P in projective coordinates
let point_mul_lambda (p:S.proj_point) : S.proj_point =
  let (_X, _Y, _Z) = p in (S.(beta *% _X), _Y, _Z)

// fast computation of [lambda]G in projective coordinates
let point_mul_g_lambda () : S.proj_point =
  (S.(beta *% S.g_x), S.g_y, S.one)


val lemma_glv : p:S.proj_point ->
  Lemma (S.to_aff_point (point_mul_lambda p) = aff_point_mul lambda (S.to_aff_point p))

let lemma_glv p =
  let (pX, pY, pZ) = p in
  let (px, py) = S.to_aff_point p in
  assert (px = S.(pX /% pZ) /\ py = S.(pY /% pZ));
  let (qx, qy) = aff_point_mul lambda (px, py) in
  lemma_glv_aff (px, py);
  assert (qx = S.(beta *% px) /\ qy = py);
  assert (qx = S.(beta *% (pX /% pZ)) /\ qy = S.(pY /% pZ));

  let (rX, rY, rZ) = point_mul_lambda p in
  assert (rX = S.(beta *% pX) /\ rY = pY /\ rZ = pZ);
  let (rx, ry) = S.to_aff_point (rX, rY, rZ) in
  assert (rx = S.(rX /% rZ) /\ ry = S.(rY /% rZ));
  assert (rx = S.(beta *% pX /% pZ) /\ ry = S.(pY /% pZ));
  assert (qy = ry);
  // S.(beta *% pX /% rZ) = S.(beta *% (pX /% pZ))
  assert (S.(beta *% pX /% pZ) = S.(beta *% pX *% S.finv pZ));
  assert (S.(beta *% (pX /% pZ)) = S.(beta *% (pX *% S.finv pZ)));
  M.lemma_mul_mod_assoc #S.prime beta pX (S.finv pZ);
  assert (S.(beta *% pX *% S.finv pZ) = S.(beta *% (pX *% S.finv pZ)))


val lemma_glv_g : unit ->
  Lemma (S.to_aff_point (point_mul_g_lambda ()) = aff_point_mul_g lambda)

let lemma_glv_g () =
  let (_X, _Y, _Z) = point_mul_g_lambda () in
  assert (_X = S.(beta *% S.g_x) /\ _Y = S.g_y /\ _Z = S.one);
  let (x, y) = S.to_aff_point (_X, _Y, _Z) in
  assert (x = S.(_X /% _Z) /\ y = S.(_Y /% _Z));
  M.lemma_div_mod_prime_one #S.prime _X;
  M.lemma_div_mod_prime_one #S.prime _Y;
  assert (x = _X /\ y = _Y);
  lemma_glv_aff S.(g_x, g_y)


(**
  Representing a scalar k as (r1 + r2 * lambda) mod S.q,
  s.t. r1 and r2 are ~128 bits long
*)

let a1 : S.qelem = 0x3086d221a7d46bcde86c90e49284eb15
let minus_b1 : S.qelem = 0xe4437ed6010e88286f547fa90abfe4c3
let a2 : S.qelem = 0x114ca50f7a8e2f3f657c1108d9d44cfd8
let b2 : S.qelem = 0x3086d221a7d46bcde86c90e49284eb15

let minus_lambda : S.qelem =
  let x = 0xac9c52b33fa3cf1f5ad9e3fd77ed9ba4a880b9fc8ec739c2e0cfc810b51283cf in
  assert_norm (x = (- lambda) % S.q);
  x

let minus_b2 : S.qelem =
  let x = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE8A280AC50774346DD765CDA83DB1562C in
  assert_norm (x = (- b2) % S.q);
  x


val lemma_check_a_and_b : unit -> Lemma
  ((a1 + minus_b1 * minus_lambda) % S.q = 0 /\
   (a2 + b2 * lambda) % S.q = 0 /\
    a1 * b2 + minus_b1 * a2 = S.q)

let lemma_check_a_and_b () =
  assert (a1 * b2 + minus_b1 * a2 = S.q)

// a1 = b2
val lemma_a_and_b_fits: unit -> Lemma
  (minus_b1 < pow2 128 /\
   minus_b2 < pow2 256 /\
   b2 < pow2 126 /\
   a2 < pow2 129)

let lemma_a_and_b_fits () =
  assert (minus_b1 < pow2 128);
  assert (minus_b2 < pow2 256);
  assert_norm (b2 < pow2 126);
  assert_norm (a2 < pow2 129);
  assert_norm ((a1 + a2) / 2 < pow2 128)


let g1 : S.qelem =
  let x = 0x3086D221A7D46BCDE86C90E49284EB153DAA8A1471E8CA7FE893209A45DBB031 in
  assert_norm (pow2 384 * b2 / S.q + 1 = x);
  x

let g2 : S.qelem =
  let x = 0xE4437ED6010E88286F547FA90ABFE4C4221208AC9DF506C61571B4AE8AC47F71 in
  assert_norm (pow2 384 * minus_b1 / S.q = x);
  x


(* https://github.com/bitcoin-core/secp256k1/blob/master/sage/gen_split_lambda_constants.sage *)
let rnddiv2 x = let x = if x % 2 = 1 then x + 1 else x in x / 2
let qmul_shift a b (shift:pos) = rnddiv2 (a * b / pow2 (shift - 1))

(*---- prove that the result of `qmul_shift` < S.q ----*)

val lemma_mul_le (a b:nat) (c d:pos) : Lemma
  (requires a < c /\ b < d)
  (ensures  a * b <= c * d - c - d + 1)

let lemma_mul_le a b c d =
  calc (<=) {
    a * b;
    (<=) { Math.Lemmas.lemma_mult_le_left a b (d - 1) }
    a * (d - 1);
    (<=) { Math.Lemmas.lemma_mult_le_right (d - 1) a (c - 1) }
    (c - 1) * (d - 1);
    (==) { Math.Lemmas.distributivity_sub_left c 1 (d - 1) }
    c * (d - 1) - (d - 1);
    (==) { Math.Lemmas.distributivity_sub_right c d 1 }
    c * d - c - d + 1;
  }


val lemma_mul_lt (a b:nat) (c d:pos) : Lemma
  (requires a < c /\ b < d)
  (ensures  a * b < c * d)

let lemma_mul_lt a b c d =
  lemma_mul_le a b c d;
  assert (a * b <= c * d - c - d + 1)


val lemma_qmul_shift_1: a:S.qelem -> bound_b:nat -> b:S.qelem -> shift:nat -> Lemma
  (requires
    b < pow2 bound_b /\
    0 <= 256 + bound_b - shift /\ 256 + bound_b - shift <= 255)
  (ensures a * b / pow2 shift + 1 < S.q)

let lemma_qmul_shift_1 a bound_b b shift =
  let res = a * b / pow2 shift in
  lemma_mul_lt a b (pow2 256) (pow2 bound_b);
  Math.Lemmas.pow2_plus 256 bound_b;
  Math.Lemmas.lemma_div_lt_nat (a * b) (256 + bound_b) shift;
  Math.Lemmas.pow2_le_compat 255 (256 + bound_b - shift);
  assert (res < pow2 255);
  assert_norm (pow2 255 < S.q)


val lemma_qmul_shift_1_div2: a:S.qelem -> b:S.qelem -> shift:pos ->
  Lemma (a * b / pow2 (shift - 1) / 2 = a * b / pow2 shift)

let lemma_qmul_shift_1_div2 a b shift =
  calc (==) {
    (a * b / pow2 (shift - 1)) / 2;
    (==) { Math.Lemmas.division_multiplication_lemma (a * b) (pow2 (shift - 1)) 2 }
    a * b / (pow2 (shift - 1) * 2);
    (==) { Math.Lemmas.pow2_double_mult (shift - 1) }
    a * b / pow2 shift;
  }

val lemma_qmul_shift_lt_q: a:S.qelem -> bound_b:nat -> b:S.qelem -> shift:nat -> Lemma
  (requires
    b < pow2 bound_b /\
    0 <= 256 + bound_b - shift /\ 256 + bound_b - shift <= 255)
  (ensures qmul_shift a b shift < S.q)

let lemma_qmul_shift_lt_q a bound_b b shift =
  let res = qmul_shift a b shift in
  let res1 = a * b / pow2 (shift - 1) in

  let res2 = if res1 % 2 = 1 then res1 + 1 else res1 in
  assert (res = res2 / 2);

  if res1 % 2 = 0 then
    assert (res = res1 / 2)
  else begin
    assert (res == (res1 + 1) / 2);
    calc (==) {
      (res1 + 1) / 2;
      (==) { Math.Lemmas.euclidean_division_definition res1 2 }
      (res1 / 2 * 2 + res1 % 2 + 1) / 2;
      (==) { assert (res1 % 2 = 1) }
      (res1 / 2 * 2 + 2) / 2;
      (==) { Math.Lemmas.division_addition_lemma 2 2 (res1 / 2) }
      res1 / 2 + 1;
    } end;

  assert (res = (if res1 % 2 = 0 then res1 / 2 else res1 / 2 + 1));
  lemma_qmul_shift_1_div2 a b shift; // res1 / 2 = a * b / pow2 shift
  lemma_qmul_shift_1 a bound_b b shift // a * b / pow2 shift + 1 < S.q

(*--- end of the proof ---*)


let scalar_split_lambda (k:S.qelem) : S.qelem & S.qelem =
  assert_norm (g1 < pow2 254);
  assert_norm (g2 < pow2 256);
  // assert (k < pow2 256);
  lemma_qmul_shift_lt_q k 254 g1 384;
  lemma_qmul_shift_lt_q k 256 g2 384;
  let c1 : S.qelem = qmul_shift k g1 384 in
  let c2 : S.qelem = qmul_shift k g2 384 in

  let c1 = S.(c1 *^ minus_b1) in
  let c2 = S.(c2 *^ minus_b2) in

  let r2 = S.(c1 +^ c2) in
  let r1 = S.(k +^ r2 *^ minus_lambda) in
  r1, r2


val lemma_scalar_split_lambda_eval (k:S.qelem) :
  Lemma (let r1, r2 = scalar_split_lambda k in k = S.(r1 +^ r2 *^ lambda))

let lemma_scalar_split_lambda_eval k =
  assert_norm ((minus_lambda + lambda) % S.q = 0);

  let r1, r2 = scalar_split_lambda k in
  assert (r1 = S.(k +^ r2 *^ minus_lambda));
  calc (==) {
    (r1 + (r2 * lambda % S.q)) % S.q;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r r1 (r2 * lambda) S.q }
    (r1 + r2 * lambda) % S.q;
    (==) { }
    ((k + (r2 * minus_lambda % S.q)) % S.q + r2 * lambda) % S.q;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r k (r2 * minus_lambda) S.q }
    ((k + r2 * minus_lambda) % S.q + r2 * lambda) % S.q;
    (==) { Math.Lemmas.lemma_mod_plus_distr_l (k + r2 * minus_lambda) (r2 * lambda) S.q }
    (k + r2 * minus_lambda + r2 * lambda) % S.q;
    (==) { Math.Lemmas.distributivity_add_right r2 minus_lambda lambda }
    (k + r2 * (minus_lambda + lambda)) % S.q;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r k (r2 * (minus_lambda + lambda)) S.q }
    (k + (r2 * (minus_lambda + lambda) % S.q)) % S.q;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r r2 (minus_lambda + lambda) S.q }
    (k + (r2 * ((minus_lambda + lambda) % S.q) % S.q)) % S.q;
    (==) { }
    k % S.q;
    (==) { Math.Lemmas.small_mod k S.q }
    k;
  }


// [k]P = [r1 + r2 * lambda]P = [r1]P + [r2]([lambda]P) = [r1](x,y) + [r2](beta*x,y)
// which can be computed as a double exponentiation ([a]P + [b]Q)
let aff_point_mul_split_lambda (k:S.qelem) (p:S.aff_point) : S.aff_point =
  let r1, r2 = scalar_split_lambda k in
  S.aff_point_add (aff_point_mul r1 p) (aff_point_mul r2 (aff_point_mul_lambda p))

val lemma_aff_point_mul_split_lambda: k:S.qelem -> p:S.aff_point ->
  Lemma (aff_point_mul_split_lambda k p = aff_point_mul k p)

let lemma_aff_point_mul_split_lambda k p =
  let r1, r2 = scalar_split_lambda k in
  lemma_scalar_split_lambda_eval k;
  assert (k = S.(r1 +^ r2 *^ lambda));
  Math.Lemmas.lemma_mod_plus_distr_r r1 (r2 * lambda) S.q;
  assert (k = (r1 + r2 * lambda) % S.q);
  GL.lemma_aff_point_mul_modq (r1 + r2 * lambda) p;
  assert (aff_point_mul k p = aff_point_mul (r1 + r2 * lambda) p);
  GL.lemma_aff_point_mul_mul_add lambda r2 r1 p;
  assert (aff_point_mul k p =
    S.aff_point_add (aff_point_mul r2 (aff_point_mul lambda p)) (aff_point_mul r1 p));
  lemma_glv_aff p;
  assert (aff_point_mul k p =
    S.aff_point_add (aff_point_mul r2 (aff_point_mul_lambda p)) (aff_point_mul r1 p));
  LS.aff_point_add_comm_lemma (aff_point_mul r2 (aff_point_mul_lambda p)) (aff_point_mul r1 p)

// TODO: prove lemma_point_mul_split_lambda for projective coordinates
// TODO: prove that r1 and r2 are ~128 bits long
