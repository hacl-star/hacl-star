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

// val lambda_is_primitive_cube_root_unity: unit -> Lemma
//   (lambda <> 1 /\
//   S.(lambda *^ lambda *^ lambda = 1) /\
//   S.(lambda *^ lambda +^ lambda +^ 1 = 0))

// let lambda_is_primitive_cube_root_unity () =
//   assert (lambda <> 1);
//   assert (S.(lambda *^ lambda *^ lambda = 1));
//   assert (S.(lambda *^ lambda +^ lambda +^ 1 = 0))


// val beta_is_primitive_cube_root_unity: unit -> Lemma
//   (beta <> 1 /\
//    S.(beta *% beta *% beta = 1) /\
//    S.(beta *% beta +% beta +% 1 = 0))

// let beta_is_primitive_cube_root_unity () =
//   assert (beta <> 1);
//   assert (S.(beta *% beta *% beta = 1));
//   assert (S.(beta *% beta +% beta +% 1 = 0))

//--------------------------------------------

assume
val lemma_glv_aff : p:S.aff_point -> Lemma (aff_point_mul lambda p == aff_point_mul_lambda p)

val lemma_glv_g_aff : unit -> Lemma (aff_point_mul_g lambda == aff_point_mul_g_lambda ())
let lemma_glv_g_aff () = lemma_glv_aff S.(g_x, g_y)
// or, we can prove it by assert_norm


val lemma_glv : p:S.proj_point ->
  Lemma (S.to_aff_point (point_mul_lambda p) == aff_point_mul lambda (S.to_aff_point p))

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
  Lemma (S.to_aff_point (point_mul_g_lambda ()) == aff_point_mul_g lambda)

let lemma_glv_g () =
  SM.lemma_proj_aff_id (S.(beta *% S.g_x), S.g_y);
  lemma_glv_aff S.(g_x, g_y)

//--------------------------------------------

// val lemma_check_a_and_b : unit -> Lemma
//   ((a1 + minus_b1 * minus_lambda) % S.q = 0 /\
//    (a1 + b1 * lambda) % S.q = 0 /\
//    (a2 + b2 * lambda) % S.q = 0 /\
//     a1 * b2 + minus_b1 * a2 = S.q)

// let lemma_check_a_and_b () =
//   assert (a1 * b2 + minus_b1 * a2 = S.q)

// // a1 = b2
// val lemma_a_and_b_fits: unit -> Lemma
//   (minus_b1 < pow2 128 /\
//    minus_b2 < pow2 256 /\
//    b1 < pow2 256 /\
//    b2 < pow2 126 /\
//    a2 < pow2 129)

// let lemma_a_and_b_fits () =
//   assert (minus_b1 < pow2 128);
//   assert (minus_b2 < pow2 256);
//   assert_norm (b2 < pow2 126);
//   assert_norm (a2 < pow2 129);
//   assert_norm ((a1 + a2) / 2 < pow2 128)

//--------------------------------------------

val lemma_scalar_split_lambda_eval (k:S.qelem) :
  Lemma (let r1, r2 = scalar_split_lambda k in k == S.(r1 +^ r2 *^ lambda))

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
  (requires (c * d + e) % n == 0)
  (ensures  (a + b * c * d) % n == (a - e * b) % n)

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
    r1 == k1 % S.q /\ r2 == k2 % S.q)

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


// val lemma_ecmult_endo_split: k:S.qelem -> p:S.proj_point ->
//   Lemma (let r1, p1, r2, p2 = ecmult_endo_split k p in
//     let lambda_p = point_mul_lambda p in
//     let r1_0, r2_0 = scalar_split_lambda k in
//     let is_high1 = S.scalar_is_high r1_0 in
//     let is_high2 = S.scalar_is_high r2_0 in
//     p1 == (if is_high1 then S.point_negate p else p) /\
//     p2 == (if is_high2 then S.point_negate lambda_p else lambda_p))

// let lemma_ecmult_endo_split k p = ()


// TODO: prove that r1 and r2 are ~128 bits long
assume
val lemma_scalar_split_lambda_fits (k:S.qelem) (p:S.proj_point) :
  Lemma (let r1, p1, r2, p2 = ecmult_endo_split k p in
    r1 < pow2 128 /\ r2 < pow2 128)

(**
 Fast computation of [k]P in affine coordinates
*)

val lemma_aff_point_mul_split_lambda: k:S.qelem -> p:S.aff_point ->
  Lemma (let r1, r2 = scalar_split_lambda k in aff_point_mul k p ==
    S.aff_point_add (aff_point_mul r1 p) (aff_point_mul r2 (aff_point_mul_lambda p)))

let lemma_aff_point_mul_split_lambda k p =
  let r1, r2 = scalar_split_lambda k in
  calc (==) {
    aff_point_mul k p;
    (==) { lemma_scalar_split_lambda_eval k }
    aff_point_mul S.(r1 +^ r2 *^ lambda) p;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r r1 (r2 * lambda) S.q }
    aff_point_mul ((r1 + r2 * lambda) % S.q) p;
    (==) { SM.lemma_aff_point_mul_neg_modq (r1 + r2 * lambda) p }
    aff_point_mul (r1 + r2 * lambda) p;
    (==) { SM.lemma_aff_point_mul_neg_mul_add lambda r2 r1 p }
    S.aff_point_add (aff_point_mul r2 (aff_point_mul lambda p)) (aff_point_mul r1 p);
    (==) { lemma_glv_aff p }
    S.aff_point_add (aff_point_mul r2 (aff_point_mul_lambda p)) (aff_point_mul r1 p);
    (==) { LS.aff_point_add_comm_lemma (aff_point_mul r2 (aff_point_mul_lambda p)) (aff_point_mul r1 p) }
    S.aff_point_add (aff_point_mul r1 p) (aff_point_mul r2 (aff_point_mul_lambda p));
  }


val lemma_aff_point_mul_neg: r:S.qelem -> p:S.aff_point ->
  Lemma (aff_point_mul ((- r) % S.q) (S.aff_point_negate p) == aff_point_mul r p)

let lemma_aff_point_mul_neg r p =
  let cm = S.mk_k256_comm_monoid in
  let ag = S.mk_k256_abelian_group in
  let p_neg = S.aff_point_negate p in
  if r > 0 then begin
    calc (==) {
      aff_point_mul ((- r) % S.q) p_neg;
      (==) { SM.lemma_aff_point_mul_neg_modq (- r) p_neg }
      SM.aff_point_mul_neg (- r) p_neg;
      (==) { }
      S.aff_point_negate (aff_point_mul r p_neg);
      (==) { LE.lemma_inverse_pow ag p r }
      S.aff_point_negate (S.aff_point_negate (aff_point_mul r p));
      (==) { LE.lemma_inverse_id ag (aff_point_mul r p) }
      aff_point_mul r p;
    } end
  else begin
    LE.lemma_pow0 cm p;
    LE.lemma_pow0 cm p_neg end


// [k]P = [r1 + r2 * lambda]P = [r1]P + [r2]([lambda]P) = [r1](x,y) + [r2](beta*x,y)
// which can be computed as a double exponentiation ([a]P + [b]Q)
let aff_point_mul_endo_split (k:S.qelem) (p:S.aff_point) : S.aff_point =
  let r1, p1, r2, p2 = aff_ecmult_endo_split k p in
  S.aff_point_add (aff_point_mul r1 p1) (aff_point_mul r2 p2)

val lemma_aff_point_mul_endo_split: k:S.qelem -> p:S.aff_point ->
  Lemma (aff_point_mul_endo_split k p == aff_point_mul k p)

let lemma_aff_point_mul_endo_split k p =
  let r10, r20 = scalar_split_lambda k in
  let lambda_p = aff_point_mul_lambda p in
  let r1, p1 = aff_negate_point_and_scalar_cond r10 p in
  let r2, p2 = aff_negate_point_and_scalar_cond r20 lambda_p in
  assert ((r1, p1, r2, p2) == aff_ecmult_endo_split k p);
  let is_high1 = S.scalar_is_high r10 in
  let is_high2 = S.scalar_is_high r20 in

  if is_high1 && is_high2 then begin
    lemma_aff_point_mul_neg r10 p;
    lemma_aff_point_mul_neg r20 lambda_p;
    lemma_aff_point_mul_split_lambda k p end
  else begin
    if is_high1 && not is_high2 then begin
      lemma_aff_point_mul_neg r10 p;
      lemma_aff_point_mul_split_lambda k p end
    else begin
      if not is_high1 && is_high2 then begin
      lemma_aff_point_mul_neg r20 lambda_p;
      lemma_aff_point_mul_split_lambda k p end
      else lemma_aff_point_mul_split_lambda k p
    end
  end


(**
 Fast computation of [k]P in projective coordinates
*)

val lemma_ecmult_endo_split_to_aff: k:S.qelem -> p:S.proj_point -> Lemma
  (let r1, p1, r2, p2 = ecmult_endo_split k p in
   let ar1, ap1, ar2, ap2 = aff_ecmult_endo_split k (S.to_aff_point p) in
   r1 == ar1 /\ S.to_aff_point p1 == ap1 /\ r2 == ar2 /\ S.to_aff_point p2 == ap2)

let lemma_ecmult_endo_split_to_aff k p =
  let r1, p1, r2, p2 = ecmult_endo_split k p in
  let ar1, ap1, ar2, ap2 = aff_ecmult_endo_split k (S.to_aff_point p) in
  assert (r1 == ar1 /\ r2 == ar2);

  let r10, r20 = scalar_split_lambda k in
  let p_aff = S.to_aff_point p in

  let lambda_p = point_mul_lambda p in
  let lambda_p_aff = aff_point_mul_lambda p_aff in
  lemma_glv p; lemma_glv_aff p_aff;
  assert (S.to_aff_point lambda_p == lambda_p_aff);

  let is_high1 = S.scalar_is_high r10 in
  let is_high2 = S.scalar_is_high r20 in
  if not is_high1 && not is_high2 then ()
  else begin
    if not is_high1 && is_high2 then
      LS.to_aff_point_negate_lemma lambda_p
    else begin
      if is_high1 && not is_high2 then
        LS.to_aff_point_negate_lemma p
      else begin
        LS.to_aff_point_negate_lemma p;
        LS.to_aff_point_negate_lemma lambda_p
      end
    end
  end


// [k]P
let aff_proj_point_mul_split_lambda (k:S.qelem) (p:S.proj_point) : S.aff_point =
  let r1, p1, r2, p2 = ecmult_endo_split k p in
  lemma_scalar_split_lambda_fits k p;
  SE.exp_double_fw SM.aff_mk_k256_concrete_ops (S.to_aff_point p1) 128 r1 (S.to_aff_point p2) r2 4


val lemma_aff_proj_point_mul_split_lambda: k:S.qelem -> p:S.proj_point ->
  Lemma (aff_proj_point_mul_split_lambda k p == aff_point_mul k (S.to_aff_point p))

let lemma_aff_proj_point_mul_split_lambda k p =
  let r1, p1, r2, p2 = ecmult_endo_split k p in
  lemma_scalar_split_lambda_fits k p;

  let p_aff  = S.to_aff_point p in
  let p1_aff = S.to_aff_point p1 in
  let p2_aff = S.to_aff_point p2 in
  calc (==) {
    aff_proj_point_mul_split_lambda k p;
    (==) {
      SE.exp_double_fw_lemma SM.aff_mk_k256_concrete_ops p1_aff 128 r1 p2_aff r2 4;
      LE.exp_double_fw_lemma S.mk_k256_comm_monoid p1_aff 128 r1 p2_aff r2 4 }
    S.aff_point_add (aff_point_mul r1 p1_aff) (aff_point_mul r2 p2_aff);
    (==) { lemma_aff_point_mul_endo_split k p_aff; lemma_ecmult_endo_split_to_aff k p }
    aff_point_mul k p_aff;
  }


(**
  Fast computation of [k1]P1 + [k2]P2 in projective coordinates
*)

// [k1]P1 + [k2]P2 = [r11 + r12 * lambda]P1 + [r21 + r22 * lambda]P2
// = [r11]P1 + [r12]([lambda]P1) + [r21]P2 + [r22]([lambda]P2)
// = [r11](p1_x, p1_y) + [r12](beta * p1_x, p1_y) + [r21](p2_x, p2_y) + [r22](beta * p2_x, p2_y)
let point_mul_double_split_lambda
  (k1:S.qelem) (p1:S.proj_point) (k2:S.qelem) (p2:S.proj_point) : S.proj_point =
  let r11, p11, r12, p12 = ecmult_endo_split k1 p1 in
  let r21, p21, r22, p22 = ecmult_endo_split k2 p2 in
  lemma_scalar_split_lambda_fits k1 p1;
  lemma_scalar_split_lambda_fits k2 p2;
  SE.exp_four_fw S.mk_k256_concrete_ops p11 128 r11 p12 r12 p21 r21 p22 r22 4


val lemma_point_mul_double_split_lambda:
  k1:S.qelem -> p1:S.proj_point -> k2:S.qelem -> p2:S.proj_point ->
  Lemma (S.to_aff_point (point_mul_double_split_lambda k1 p1 k2 p2) ==
    S.aff_point_add (aff_point_mul k1 (S.to_aff_point p1)) (aff_point_mul k2 (S.to_aff_point p2)))

let lemma_point_mul_double_split_lambda k1 p1 k2 p2 =
  let open Spec.K256 in
  let r11, p11, r12, p12 = ecmult_endo_split k1 p1 in
  let r21, p21, r22, p22 = ecmult_endo_split k2 p2 in
  lemma_scalar_split_lambda_fits k1 p1;
  lemma_scalar_split_lambda_fits k2 p2;

  let p1_aff = to_aff_point p1 in
  let p2_aff = to_aff_point p2 in
  let p11_aff = to_aff_point p11 in
  let p12_aff = to_aff_point p12 in
  let p21_aff = to_aff_point p21 in
  let p22_aff = to_aff_point p22 in

  calc (==) {
    S.to_aff_point (point_mul_double_split_lambda k1 p1 k2 p2);
  (==) {
    SE.exp_four_fw_lemma mk_k256_concrete_ops p11 128 r11 p12 r12 p21 r21 p22 r22 4;
    LE.exp_four_fw_lemma mk_k256_comm_monoid p11_aff 128 r11 p12_aff r12 p21_aff r21 p22_aff r22 4}
    S.aff_point_add
      (S.aff_point_add
        (S.aff_point_add (aff_point_mul r11 p11_aff) (aff_point_mul r12 p12_aff))
        (aff_point_mul r21 p21_aff))
      (aff_point_mul r22 p22_aff);
    (==) { lemma_aff_point_mul_endo_split k1 p1_aff; lemma_ecmult_endo_split_to_aff k1 p1 }
    S.aff_point_add
      (S.aff_point_add (aff_point_mul k1 p1_aff) (aff_point_mul r21 p21_aff))
      (aff_point_mul r22 p22_aff);
    (==) { LS.aff_point_add_assoc_lemma
      (aff_point_mul k1 p1_aff) (aff_point_mul r21 p21_aff) (aff_point_mul r22 p22_aff) }
    S.aff_point_add (aff_point_mul k1 p1_aff)
      (S.aff_point_add (aff_point_mul r21 p21_aff) (aff_point_mul r22 p22_aff));
    (==) { lemma_aff_point_mul_endo_split k2 p2_aff; lemma_ecmult_endo_split_to_aff k2 p2 }
    S.aff_point_add (aff_point_mul k1 p1_aff) (aff_point_mul k2 p2_aff);
  }

//-----------------------------------

// [k]P or -[k]P = [k](-P)
val aff_point_negate_cond_pow_lemma: is_negate:bool -> p:S.proj_point -> k:nat ->
  Lemma (let co = SM.aff_mk_k256_concrete_ops in
    aff_point_negate_cond (SE.pow co (S.to_aff_point p) k) is_negate ==
    SE.pow co (S.to_aff_point (point_negate_cond p is_negate)) k)

let aff_point_negate_cond_pow_lemma is_negate p k =
  let co = SM.aff_mk_k256_concrete_ops in
  let cm = S.mk_k256_comm_monoid in
  let p_aff = S.to_aff_point p in

  if is_negate then
    calc (==) {
      S.aff_point_negate (SE.pow co p_aff k);
      (==) { SE.pow_lemma co p_aff k }
      S.aff_point_negate (LE.pow cm p_aff k);
      (==) { LE.lemma_inverse_pow S.mk_k256_abelian_group p_aff k }
      LE.pow cm (S.aff_point_negate p_aff) k;
      (==) { SE.pow_lemma co (S.aff_point_negate p_aff) k }
      SE.pow co (S.aff_point_negate p_aff) k;
      (==) { LS.to_aff_point_negate_lemma p }
      SE.pow co (S.to_aff_point (S.point_negate p)) k;
    }
  else ()


// [k]([lambda]P) = [lambda]([k]P) or [k](-[lambda]P) = [lambda](-[k]P)
val aff_point_negate_cond_lambda_pow_lemma: is_negate:bool -> p:S.proj_point -> k:nat ->
  Lemma (let co = SM.aff_mk_k256_concrete_ops in
    aff_point_mul lambda (aff_point_negate_cond (SE.pow co (S.to_aff_point p) k) is_negate) ==
    SE.pow co (S.to_aff_point (point_negate_cond (point_mul_lambda p) is_negate)) k)

let aff_point_negate_cond_lambda_pow_lemma is_negate p k =
  let co = SM.aff_mk_k256_concrete_ops in
  let cm = S.mk_k256_comm_monoid in
  let ag = S.mk_k256_abelian_group in
  let p_aff = S.to_aff_point p in
  let p_lambda = point_mul_lambda p in
  let p_lambda_aff = S.to_aff_point p_lambda in

  if is_negate then
    calc (==) {
      aff_point_mul lambda (S.aff_point_negate (SE.pow co p_aff k));
      (==) { SE.pow_lemma co p_aff k }
      aff_point_mul lambda (S.aff_point_negate (LE.pow cm p_aff k));
      (==) { LE.lemma_inverse_pow ag (LE.pow cm p_aff k) lambda }
      S.aff_point_negate (LE.pow cm (LE.pow cm p_aff k) lambda);
      (==) { LE.lemma_pow_mul cm p_aff k lambda }
      S.aff_point_negate (LE.pow cm p_aff (k * lambda));
      (==) { LE.lemma_pow_mul cm p_aff lambda k }
      S.aff_point_negate (LE.pow cm (LE.pow cm p_aff lambda) k);
      (==) { LE.lemma_inverse_pow ag (LE.pow cm p_aff lambda) k }
      LE.pow cm (S.aff_point_negate (LE.pow cm p_aff lambda)) k;
      (==) { lemma_glv p }
      LE.pow cm (S.aff_point_negate (S.to_aff_point p_lambda)) k;
      (==) { LS.to_aff_point_negate_lemma p_lambda }
      LE.pow cm (S.to_aff_point (S.point_negate p_lambda)) k;
      (==) { SE.pow_lemma co (S.to_aff_point (S.point_negate p_lambda)) k }
      SE.pow co (S.to_aff_point (S.point_negate p_lambda)) k;
    }
  else
    calc (==) {
      aff_point_mul lambda (SE.pow co p_aff k);
      (==) { SE.pow_lemma co p_aff k }
      aff_point_mul lambda (LE.pow cm p_aff k);
      (==) { LE.lemma_pow_mul cm p_aff k lambda }
      LE.pow cm p_aff (k * lambda);
      (==) { LE.lemma_pow_mul cm p_aff lambda k }
      LE.pow cm (LE.pow cm p_aff lambda) k;
      (==) { lemma_glv p }
      LE.pow cm p_lambda_aff k;
      (==) { SE.pow_lemma co p_lambda_aff k }
      SE.pow co p_lambda_aff k;
    }
