module Hacl.Spec.K256.GLV.Lemmas1

open FStar.Mul

module M = Lib.NatMod
module S = Spec.K256
open Hacl.Spec.K256.GLV

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(*
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
*)

(*
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
*)

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
    let k2 = c1 * minus_b1 - c2 * b2 in
    r1 == k1 % S.q /\ r2 == k2 % S.q)

let lemma_scalar_split_lambda_r1_and_r2 k =
  qmul_shift_384_lemma k g1;
  qmul_shift_384_lemma k g2;
  let c1 : S.qelem = qmul_shift_384 k g1 in
  let c2 : S.qelem = qmul_shift_384 k g2 in

  let r1, r2 = scalar_split_lambda k in
  assert (r2 = S.((c1 *^ minus_b1 +^ c2 *^ minus_b2) % q));
  assert (r1 = S.(k +^ r2 *^ minus_lambda));

  let k2 = c1 * minus_b1 - c2 * b2 in
  calc (==) { // r2
    S.(c1 *^ minus_b1 +^ c2 *^ minus_b2) % S.q;
    (==) { }
    ((c1 * minus_b1 % S.q) + (c2 * minus_b2 % S.q)) % S.q;
    (==) { assert_norm (minus_b2 = (- b2) % S.q) }
    ((c1 * minus_b1 % S.q) + (c2 * ((- b2) % S.q) % S.q)) % S.q;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r c2 (- b2) S.q }
    ((c1 * minus_b1 % S.q) + (c2 * (-b2) % S.q)) % S.q;
    (==) { Math.Lemmas.lemma_mod_plus_distr_l (c1 * minus_b1) (c2 * (-b2) % S.q) S.q }
    (c1 * minus_b1 + (c2 * (-b2) % S.q)) % S.q;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r (c1 * minus_b1) (c2 * (-b2)) S.q }
    (c1 * minus_b1 + c2 * (-b2)) % S.q;
    (==) { Math.Lemmas.neg_mul_right c2 b2 }
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
    (k + (c1 * minus_b1 - c2 * b2) * minus_lambda) % S.q;
    (==) { Math.Lemmas.distributivity_sub_left (c1 * minus_b1) (c2 * b2) minus_lambda }
    (k + c1 * minus_b1 * minus_lambda - c2 * b2 * minus_lambda) % S.q;
    (==) {
      assert_norm ((minus_b1 * minus_lambda + a1) % S.q = 0);
      lemma_mod_add_mul_zero (k - c2 * b2 * minus_lambda) c1 minus_b1 minus_lambda a1 S.q }
    (k - c2 * b2 * minus_lambda - a1 * c1) % S.q;
    (==) {
      assert_norm ((-b2 * minus_lambda + a2) % S.q = 0);
      lemma_mod_add_mul_zero (k - a1 * c1) c2 (-b2) minus_lambda a2 S.q }
    (k - a1 * c1 - a2 * c2) % S.q;
    (==) { }
    k1 % S.q;
  }


val lemma_scalar_split_lambda_fits (k:S.qelem) (p:S.proj_point) :
  Lemma (let r1, p1, r2, p2 = ecmult_endo_split k p in
    r1 < pow2 128 /\ r2 < pow2 128)

let lemma_scalar_split_lambda_fits k p =
  let r1, r2 = scalar_split_lambda k in
  let lambda_p = point_mul_lambda p in
  let r1_cneg, p1_cneg = negate_point_and_scalar_cond r1 p in
  let r2_cneg, p2_cneg = negate_point_and_scalar_cond r2 lambda_p in

  let r1_s, p1_s, r2_s, p2_s = ecmult_endo_split k p in
  assert (r1_s == r1_cneg /\ p1_s == p1_cneg);
  assert (r2_s == r2_cneg /\ p2_s == p2_cneg);

  assert (r1_cneg = (if r1 > S.q / 2 then (-r1) % S.q else r1));
  assert (r2_cneg = (if r2 > S.q / 2 then (-r2) % S.q else r2));

  lemma_scalar_split_lambda_r1_and_r2 k;
  let c1 = qmul_shift_384 k g1 in
  let c2 = qmul_shift_384 k g2 in

  let k1 = k - a1 * c1 - a2 * c2 in
  let k2 = c1 * minus_b1 - c2 * b2 in // or: k2 = - b1 * c1 - b2 * c2
  assert (r1 == k1 % S.q /\ r2 == k2 % S.q);
  assert_norm (g1 = pow2 384 * b2 / S.q + 1);
  assert_norm (g2 = pow2 384 * minus_b1 / S.q);

  let rem1 = k * g1 / pow2 383 % 2 in
  let rem2 = k * g2 / pow2 383 % 2 in
  assert (c1 == k * g1 / pow2 384 + rem1);
  assert (c2 == k * g2 / pow2 384 + rem2); admit()
