module Hacl.Spec.K256.GLV

open FStar.Mul

module S = Spec.K256

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

// For more comments see https://github.com/bitcoin-core/secp256k1/blob/master/src/scalar_impl.h

(**
 Fast computation of [lambda]P as (beta * x, y) in affine and projective coordinates
*)

let lambda : S.qelem = 0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72

let beta : S.felem = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee

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

// fast computation of [lambda]P in projective coordinates
let point_mul_lambda (p:S.proj_point) : S.proj_point =
  let (_X, _Y, _Z) = p in (S.(beta *% _X), _Y, _Z)

// fast computation of [lambda]G in projective coordinates
let point_mul_g_lambda () : S.proj_point =
  (S.(beta *% S.g_x), S.g_y, S.one)

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


(**
 Fast computation of [k]P in affine coordinates
*)

let aff_point_negate_cond (p:S.aff_point) (is_negate:bool) : S.aff_point =
  if is_negate then S.aff_point_negate p else p

let aff_negate_point_and_scalar_cond (k:S.qelem) (p:S.aff_point) : S.qelem & S.aff_point =
  if S.scalar_is_high k then begin
    let k_neg = S.qnegate k in
    let p_neg = S.aff_point_negate p in
    k_neg, p_neg end
  else k, p

// https://github.com/bitcoin-core/secp256k1/blob/master/src/ecmult_impl.h
// [k]P = [r1 + r2 * lambda]P = [r1]P + [r2]([lambda]P) = [r1](x,y) + [r2](beta*x,y)
let aff_ecmult_endo_split (k:S.qelem) (p:S.aff_point) :
  S.qelem & S.aff_point & S.qelem & S.aff_point
 =
  let r1, r2 = scalar_split_lambda k in
  let lambda_p = aff_point_mul_lambda p in
  let r1, p1 = aff_negate_point_and_scalar_cond r1 p in
  let r2, p2 = aff_negate_point_and_scalar_cond r2 lambda_p in
  (r1, p1, r2, p2)


(**
 Fast computation of [k]P in projective coordinates
*)

let point_negate_cond (p:S.proj_point) (is_negate:bool) : S.proj_point =
  if is_negate then S.point_negate p else p

let negate_point_and_scalar_cond (k:S.qelem) (p:S.proj_point) : S.qelem & S.proj_point =
  if S.scalar_is_high k then begin
    let k_neg = S.qnegate k in
    let p_neg = S.point_negate p in
    k_neg, p_neg end
  else k, p


let ecmult_endo_split (k:S.qelem) (p:S.proj_point) :
  S.qelem & S.proj_point & S.qelem & S.proj_point
 =
  let r1, r2 = scalar_split_lambda k in
  let lambda_p = point_mul_lambda p in
  let r1, p1 = negate_point_and_scalar_cond r1 p in
  let r2, p2 = negate_point_and_scalar_cond r2 lambda_p in
  (r1, p1, r2, p2)
