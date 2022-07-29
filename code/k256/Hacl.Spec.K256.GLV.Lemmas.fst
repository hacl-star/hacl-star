module Hacl.Spec.K256.GLV.Lemmas

open FStar.Mul

module M = Lib.NatMod
module LE = Lib.Exponentiation
module SE = Spec.Exponentiation

module S = Spec.K256
module LS = Spec.K256.Lemmas
module SM = Hacl.Spec.K256.ECSM.Lemmas

open Hacl.Spec.K256.GLV

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val lambda_is_primitive_cube_root_unity: unit -> Lemma
  (lambda <> 1 /\
  S.(lambda *^ lambda *^ lambda = 1) /\
  S.(lambda *^ lambda +^ lambda +^ 1 = 0))

let lambda_is_primitive_cube_root_unity () =
  assert (lambda <> 1);
  assert (S.(lambda *^ lambda *^ lambda = 1));
  assert (S.(lambda *^ lambda +^ lambda +^ 1 = 0))


val beta_is_primitive_cube_root_unity: unit -> Lemma
  (beta <> 1 /\
   S.(beta *% beta *% beta = 1) /\
   S.(beta *% beta +% beta +% 1 = 0))

let beta_is_primitive_cube_root_unity () =
  assert (beta <> 1);
  assert (S.(beta *% beta *% beta = 1));
  assert (S.(beta *% beta +% beta +% 1 = 0))

assume
val lemma_glv_aff : p:S.aff_point -> Lemma (aff_point_mul lambda p = aff_point_mul_lambda p)

val lemma_glv_g_aff : unit -> Lemma (aff_point_mul_g lambda = aff_point_mul_g_lambda ())
let lemma_glv_g_aff () = lemma_glv_aff S.(g_x, g_y)
// or, we can prove it by assert_norm


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
    (==) { SM.lemma_aff_point_mul_modq (r1 + r2 * lambda) p }
    aff_point_mul (r1 + r2 * lambda) p;
    (==) { SM.lemma_aff_point_mul_mul_add lambda r2 r1 p }
    S.aff_point_add (aff_point_mul r2 (aff_point_mul lambda p)) (aff_point_mul r1 p);
    (==) { lemma_glv_aff p }
    S.aff_point_add (aff_point_mul r2 (aff_point_mul_lambda p)) (aff_point_mul r1 p);
    (==) { LS.aff_point_add_comm_lemma (aff_point_mul r2 (aff_point_mul_lambda p)) (aff_point_mul r1 p) }
    S.aff_point_add (aff_point_mul r1 p) (aff_point_mul r2 (aff_point_mul_lambda p));
  }


(**
 Fast computation of [k]P in projective coordinates
*)

// [k]P
let point_mul_split_lambda (k:S.qelem) (p:S.proj_point) : S.proj_point =
  let r1, r2 = scalar_split_lambda k in
  lemma_scalar_split_lambda_fits k;
  SE.exp_double_fw S.mk_k256_concrete_ops p 129 r1 (point_mul_lambda p) r2 4

// [k]G
let point_mul_g_split_lambda (k:S.qelem) : S.proj_point =
  let r1, r2 = scalar_split_lambda k in
  lemma_scalar_split_lambda_fits k;
  SE.exp_double_fw S.mk_k256_concrete_ops S.g 129 r1 (point_mul_g_lambda ()) r2 4

// TODO: add exp_four_fw?
// [a1]G + [a2]P
let point_mul_double_g (a1:S.qelem) (a2:S.qelem) (p:S.proj_point) : S.proj_point =
  let a1_r1, a1_r2 = scalar_split_lambda a1 in
  let a2_r1, a2_r2 = scalar_split_lambda a2 in
  S.point_add
    S.(point_add (point_mul_g a1_r1) (point_mul a1_r2 (point_mul_g_lambda ())))
    S.(point_add (point_mul a2_r1 p) (point_mul a2_r2 (point_mul_lambda p)))


val lemma_point_mul_split_lambda: k:S.qelem -> p:S.proj_point ->
  Lemma (S.to_aff_point (point_mul_split_lambda k p) = aff_point_mul k (S.to_aff_point p))

let lemma_point_mul_split_lambda k p =
  let open Spec.K256 in
  let r1, r2 = scalar_split_lambda k in
  lemma_scalar_split_lambda_fits k;
  let p_aff = to_aff_point p in
  calc (==) {
    to_aff_point (point_mul_split_lambda k p);
    (==) {
      SE.exp_double_fw_lemma mk_k256_concrete_ops p 129 r1 (point_mul_lambda p) r2 4;
      LE.exp_double_fw_lemma mk_k256_comm_monoid
        p_aff 129 r1 (to_aff_point (point_mul_lambda p)) r2 4 }
    aff_point_add
      (aff_point_mul r1 p_aff) (aff_point_mul r2 (to_aff_point (point_mul_lambda p)));
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
  SM.lemma_proj_aff_id p
