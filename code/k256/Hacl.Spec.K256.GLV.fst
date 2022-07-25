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

let b1 : S.qelem =
  let x = 0xfffffffffffffffffffffffffffffffdd66b5e10ae3a1813507ddee3c5765c7e in
  assert_norm (x = (- minus_b1) % S.q);
  x

let minus_b2 : S.qelem =
  let x = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE8A280AC50774346DD765CDA83DB1562C in
  assert_norm (x = (- b2) % S.q);
  x


val lemma_check_a_and_b : unit -> Lemma
  ((a1 + minus_b1 * minus_lambda) % S.q = 0 /\
   (a1 + b1 * lambda) % S.q = 0 /\
   (a2 + b2 * lambda) % S.q = 0 /\
    a1 * b2 + minus_b1 * a2 = S.q)

let lemma_check_a_and_b () =
  assert (a1 * b2 + minus_b1 * a2 = S.q)

// a1 = b2
val lemma_a_and_b_fits: unit -> Lemma
  (minus_b1 < pow2 128 /\
   minus_b2 < pow2 256 /\
   b1 < pow2 256 /\
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

let qmul_shift_384 a b =
  a * b / pow2 384 + (a * b / pow2 383 % 2)

val qmul_shift_384_lemma (a b:S.qelem) : Lemma (qmul_shift_384 a b < S.q)
let qmul_shift_384_lemma a b =
  assert_norm (S.q < pow2 256);
  Math.Lemmas.lemma_mult_lt_sqr a b (pow2 256);
  Math.Lemmas.pow2_plus 256 256;
  assert (a * b < pow2 512);
  Math.Lemmas.lemma_div_lt_nat (a * b) 512 384;
  assert (a * b / pow2 384 < pow2 128);
  assert_norm (pow2 128 < S.q)


let scalar_split_lambda (k:S.qelem) : S.qelem & S.qelem =
  qmul_shift_384_lemma k g1;
  qmul_shift_384_lemma k g2;
  let c1 : S.qelem = qmul_shift_384 k g1 in
  let c2 : S.qelem = qmul_shift_384 k g2 in

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


val lemma_mod_add_mul_zero (a b c d e:int) (n:pos) : Lemma
  (requires (c * d + e) % n = 0)
  (ensures  (a + b * c * d) % n = (a - e * b) % n)

let lemma_mod_add_mul_zero a b c d e n =
  calc (==) {
    (a + b * c * d) % n;
    (==) { assert ((c * d + e) % n * b % n = 0) }
    (a + b * c * d - ((c * d + e) % n) * b % n) % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (c * d + e) b n }
    (a + b * c * d - (c * d + e) * b % n) % n;
    (==) { Math.Lemmas.lemma_mod_sub_distr (a + b * c * d) ((c * d + e) * b) n }
    (a + b * c * d - (c * d + e) * b) % n;
    (==) { Math.Lemmas.distributivity_add_left (c * d) e b }
    (a + b * c * d - (c * d * b + e * b)) % n;
    (==) { Math.Lemmas.paren_mul_right b c d; Math.Lemmas.swap_mul b (c * d) }
    (a + c * d * b - (c * d * b + e * b)) % n;
    (==) { }
    (a - e * b) % n;
  }


val lemma_scalar_split_lambda_r1_and_r2 (k:S.qelem) :
  Lemma (let r1, r2 = scalar_split_lambda k in
    let c1 = qmul_shift_384 k g1 in
    let c2 = qmul_shift_384 k g2 in
    let k1 = k - a1 * c1 - a2 * c2 in
    let k2 = c1 * minus_b1 + c2 * minus_b2 in // or: k2 = - b1 * c1 - b2 * c2
    r1 = k1 % S.q /\ r2 = k2 % S.q)

let lemma_scalar_split_lambda_r1_and_r2 k =
  qmul_shift_384_lemma k g1;
  qmul_shift_384_lemma k g2;
  let c1 : S.qelem = qmul_shift_384 k g1 in
  let c2 : S.qelem = qmul_shift_384 k g2 in

  let r1, r2 = scalar_split_lambda k in
  assert (r2 = S.(c1 *^ minus_b1 +^ c2 *^ minus_b2));
  assert (r1 = S.(k +^ r2 *^ minus_lambda));

  // let k2 = - c1 * b1 - c2 * b2 in
  // calc (==) { // r2
  //   S.(c1 *^ minus_b1 +^ c2 *^ minus_b2);
  //   (==) { assert_norm (minus_b1 = (-b1) % S.q) }
  //   S.(c1 *^ ((-b1) % S.q) +^ c2 *^ minus_b2);
  //   (==) { assert_norm (minus_b2 = (-b2) % S.q) }
  //   S.(c1 *^ ((-b1) % S.q) +^ c2 *^ ((-b2) % S.q));
  //   (==) { }
  //   ((c1 * ((-b1) % S.q) % S.q) + (c2 * ((-b2) % S.q) % S.q)) % S.q;
  //   (==) { Math.Lemmas.lemma_mod_mul_distr_r c1 (-b1) S.q }
  //   ((c1 * (-b1) % S.q) + (c2 * ((-b2) % S.q) % S.q)) % S.q;
  //   (==) { Math.Lemmas.lemma_mod_mul_distr_r c2 (-b2) S.q }
  //   ((c1 * (-b1) % S.q) + (c2 * (-b2) % S.q)) % S.q;
  //   (==) { Math.Lemmas.lemma_mod_plus_distr_l (c1 * (-b1)) (c2 * (-b2) % S.q) S.q }
  //   (c1 * (-b1) + (c2 * (-b2) % S.q)) % S.q;
  //   (==) { Math.Lemmas.lemma_mod_plus_distr_r (c1 * (-b1)) (c2 * (-b2)) S.q }
  //   (c1 * (-b1) + c2 * (-b2)) % S.q;
  //   (==) { Math.Lemmas.neg_mul_right c1 b1 }
  //   (- c1 * b1 + c2 * (-b2)) % S.q;
  //   (==) { Math.Lemmas.neg_mul_right c2 b2 }
  //   (- c1 * b1 - c2 * b2) % S.q;
  //   (==) { }
  //   k2 % S.q;
  //   };

  // let k1 = k - a1 * c1 - a2 * c2 in
  // calc (==) { // r1
  //   S.(k +^ r2 *^ minus_lambda);
  //   (==) { }
  //   (k + ((k2 % S.q) * minus_lambda % S.q)) % S.q;
  //   (==) { Math.Lemmas.lemma_mod_mul_distr_l k2 minus_lambda S.q }
  //   (k + (k2 * minus_lambda % S.q)) % S.q;
  //   (==) { assert_norm (minus_lambda = (- lambda) % S.q) }
  //   (k + (k2 * ((- lambda) % S.q) % S.q)) % S.q;
  //   (==) { Math.Lemmas.lemma_mod_mul_distr_r k2 (- lambda) S.q }
  //   (k + (k2 * (- lambda) % S.q)) % S.q;
  //   (==) { Math.Lemmas.lemma_mod_plus_distr_r k (k2 * (- lambda)) S.q }
  //   (k + k2 * (- lambda)) % S.q;
  //   (==) { Math.Lemmas.neg_mul_right k2 lambda }
  //   (k - k2 * lambda) % S.q;
  //   (==) { }
  //   (k - (- c1 * b1 - c2 * b2) * lambda) % S.q;
  //   (==) { Math.Lemmas.neg_mul_left (c1 * b1 + c2 * b2) lambda }
  //   (k + (c1 * b1 + c2 * b2) * lambda) % S.q;
  //   (==) { Math.Lemmas.distributivity_add_left (c1 * b1) (c2 * b2) lambda }
  //   (k + c1 * b1 * lambda + c2 * b2 * lambda) % S.q;
  //   (==) {
  //     assert_norm ((b1 * lambda + a1) % S.q = 0);
  //     lemma_mod_add_mul_zero (k + c2 * b2 * lambda) c1 b1 lambda a1 S.q }
  //   (k + c2 * b2 * lambda - a1 * c1) % S.q;
  //   (==) {
  //     assert_norm ((b2 * lambda + a2) % S.q = 0);
  //     lemma_mod_add_mul_zero (k - a1 * c1) c2 b2 lambda a2 S.q }
  //   (k - a1 * c1 - a2 * c2) % S.q;
  //   (==) { }
  //   k1 % S.q;
  // };

  let k2 = c1 * minus_b1 + c2 * minus_b2 in
  calc (==) { // r2
    S.(c1 *^ minus_b1 +^ c2 *^ minus_b2);
    (==) { }
    ((c1 * minus_b1 % S.q) + (c2 * minus_b2 % S.q)) % S.q;
    (==) { Math.Lemmas.lemma_mod_plus_distr_l (c1 * minus_b1) (c2 * minus_b2 % S.q) S.q }
    (c1 * minus_b1 + (c2 * minus_b2 % S.q)) % S.q;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r (c1 * minus_b1) (c2 * minus_b2) S.q }
    (c1 * minus_b1 + c2 * minus_b2) % S.q;
    (==) { }
    k2 % S.q;
  };

  let k1 = k - a1 * c1 - a2 * c2 in
  calc (==) { // r1
    S.(k +^ r2 *^ minus_lambda);
    (==) { }
    (k + ((k2 % S.q) * minus_lambda % S.q)) % S.q;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l k2 minus_lambda S.q }
    (k + (k2 * minus_lambda % S.q)) % S.q;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r k (k2 * minus_lambda) S.q }
    (k + (c1 * minus_b1 + c2 * minus_b2) * minus_lambda) % S.q;
    (==) { Math.Lemmas.distributivity_add_left (c1 * minus_b1) (c2 * minus_b2) minus_lambda }
    (k + c1 * minus_b1 * minus_lambda + c2 * minus_b2 * minus_lambda) % S.q;
    (==) {
      assert_norm ((minus_b1 * minus_lambda + a1) % S.q = 0);
      lemma_mod_add_mul_zero (k + c2 * minus_b2 * minus_lambda) c1 minus_b1 minus_lambda a1 S.q }
    (k + c2 * minus_b2 * minus_lambda - a1 * c1) % S.q;
    (==) {
      assert_norm ((minus_b2 * minus_lambda + a2) % S.q = 0);
      lemma_mod_add_mul_zero (k - a1 * c1) c2 minus_b2 minus_lambda a2 S.q }
    (k - a1 * c1 - a2 * c2) % S.q;
    (==) { }
    k1 % S.q;
  }


// TODO: prove that r1 and r2 are ~128 bits long
assume
val lemma_scalar_split_lambda_fits (k:S.qelem) :
  Lemma (let r1, r2 = scalar_split_lambda k in r1 < pow2 129 /\ r2 < pow2 129)


(**
 Fast computation of [k]P in affine coordinates
*)

// [k]P = [r1 + r2 * lambda]P = [r1]P + [r2]([lambda]P) = [r1](x,y) + [r2](beta*x,y)
// which can be computed as a double exponentiation ([a]P + [b]Q)
let aff_point_mul_split_lambda (k:S.qelem) (p:S.aff_point) : S.aff_point =
  let r1, r2 = scalar_split_lambda k in
  S.aff_point_add (aff_point_mul r1 p) (aff_point_mul r2 (aff_point_mul_lambda p))

val lemma_aff_point_mul_split_lambda: k:S.qelem -> p:S.aff_point ->
  Lemma (aff_point_mul_split_lambda k p = aff_point_mul k p)

let lemma_aff_point_mul_split_lambda k p =
  let r1, r2 = scalar_split_lambda k in
  calc (==) {
    aff_point_mul k p;
    (==) { lemma_scalar_split_lambda_eval k }
    aff_point_mul S.(r1 +^ r2 *^ lambda) p;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r r1 (r2 * lambda) S.q }
    aff_point_mul ((r1 + r2 * lambda) % S.q) p;
    (==) { GL.lemma_aff_point_mul_modq (r1 + r2 * lambda) p }
    aff_point_mul (r1 + r2 * lambda) p;
    (==) { GL.lemma_aff_point_mul_mul_add lambda r2 r1 p }
    S.aff_point_add (aff_point_mul r2 (aff_point_mul lambda p)) (aff_point_mul r1 p);
    (==) { lemma_glv_aff p }
    S.aff_point_add (aff_point_mul r2 (aff_point_mul_lambda p)) (aff_point_mul r1 p);
    (==) { LS.aff_point_add_comm_lemma (aff_point_mul r2 (aff_point_mul_lambda p)) (aff_point_mul r1 p) }
    S.aff_point_add (aff_point_mul r1 p) (aff_point_mul r2 (aff_point_mul_lambda p));
  }


(**
 Fast computation of [k]P in projective coordinates
*)

// [k]P = [r1 + r2 * lambda]P = [r1]P + [r2]([lambda]P) = [r1](x,y) + [r2](beta*x,y)
// which can be computed as a double exponentiation ([a]P + [b]Q)
let point_mul_split_lambda (k:S.qelem) (p:S.proj_point) : S.proj_point =
  let r1, r2 = scalar_split_lambda k in
  S.(point_add (point_mul r1 p) (point_mul r2 (point_mul_lambda p)))


val lemma_point_mul_split_lambda: k:S.qelem -> p:S.proj_point ->
  Lemma (S.to_aff_point (point_mul_split_lambda k p) = aff_point_mul k (S.to_aff_point p))

let lemma_point_mul_split_lambda k p =
  let open Spec.K256 in
  let r1, r2 = scalar_split_lambda k in
  let p_aff = to_aff_point p in
  calc (==) {
    to_aff_point (point_mul_split_lambda k p);
    (==) { LS.to_aff_point_add_lemma (point_mul r1 p) (point_mul r2 (point_mul_lambda p)) }
    aff_point_add
      (to_aff_point (point_mul r1 p))
      (to_aff_point (point_mul r2 (point_mul_lambda p)));
    (==) { GL.lemma_point_mul r1 p }
    aff_point_add (aff_point_mul r1 p_aff) (to_aff_point (point_mul r2 (point_mul_lambda p)));
    (==) { GL.lemma_point_mul r2 (point_mul_lambda p) }
    aff_point_add (aff_point_mul r1 p_aff) (aff_point_mul r2 (to_aff_point (point_mul_lambda p)));
    (==) { lemma_glv p }
    aff_point_add (aff_point_mul r1 p_aff) (aff_point_mul r2 (aff_point_mul lambda p_aff));
    (==) { lemma_glv_aff p_aff }
    aff_point_add (aff_point_mul r1 p_aff) (aff_point_mul r2 (aff_point_mul_lambda p_aff));
    (==) { lemma_aff_point_mul_split_lambda k p_aff }
    aff_point_mul k p_aff;
  }


// TODO: what about point_at_infinity?
val lemma_point_mul_split_lambda_aff: k:S.qelem -> p:S.aff_point ->
  Lemma (S.to_aff_point (point_mul_split_lambda k (S.to_proj_point p)) = aff_point_mul k p)

let lemma_point_mul_split_lambda_aff k p =
  lemma_point_mul_split_lambda k (S.to_proj_point p);
  GL.lemma_proj_aff_id p
