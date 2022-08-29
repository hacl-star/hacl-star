module Hacl.Impl.K256.GLV.Constants

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST

module S = Spec.K256
module SG = Hacl.Spec.K256.GLV
module SGL = Hacl.Spec.K256.GLV.Lemmas

open Hacl.K256.Field
open Hacl.K256.Scalar
open Hacl.Impl.K256.Point

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val make_minus_lambda: f:qelem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    qas_nat h1 f == SG.minus_lambda)

let make_minus_lambda f =
  [@inline_let]
  let x =
   (u64 0xe0cfc810b51283cf,
    u64 0xa880b9fc8ec739c2,
    u64 0x5ad9e3fd77ed9ba4,
    u64 0xac9c52b33fa3cf1f) in

  assert_norm (SG.minus_lambda == qas_nat4 x);
  make_u64_4 f x


inline_for_extraction noextract
val make_beta: f:felem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    as_nat h1 f == SG.beta /\ inv_fully_reduced h1 f)

let make_beta f =
  [@inline_let]
  let x =
   (u64 0x96c28719501ee,
    u64 0x7512f58995c13,
    u64 0xc3434e99cf049,
    u64 0x7106e64479ea,
    u64 0x7ae96a2b657c) in

  assert_norm (0x96c28719501ee <= max52);
  assert_norm (0x7ae96a2b657c <= max48);
  assert_norm (SG.beta == as_nat5 x);
  make_u52_5 f x


inline_for_extraction noextract
val make_minus_b1: f:qelem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    qas_nat h1 f == SG.minus_b1)

let make_minus_b1 f =
  [@inline_let]
  let x =
   (u64 0x6f547fa90abfe4c3,
    u64 0xe4437ed6010e8828,
    u64 0x0,
    u64 0x0) in

  assert_norm (SG.minus_b1 == qas_nat4 x);
  make_u64_4 f x


inline_for_extraction noextract
val make_minus_b2: f:qelem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    qas_nat h1 f == SG.minus_b2)

let make_minus_b2 f =
  [@inline_let]
  let x =
   (u64 0xd765cda83db1562c,
    u64 0x8a280ac50774346d,
    u64 0xfffffffffffffffe,
    u64 0xffffffffffffffff) in

  assert_norm (SG.minus_b2 == qas_nat4 x);
  make_u64_4 f x


inline_for_extraction noextract
val make_g1: f:qelem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    qas_nat h1 f == SG.g1)

let make_g1 f =
  [@inline_let]
  let x =
   (u64 0xe893209a45dbb031,
    u64 0x3daa8a1471e8ca7f,
    u64 0xe86c90e49284eb15,
    u64 0x3086d221a7d46bcd) in

  assert_norm (SG.g1 == qas_nat4 x);
  make_u64_4 f x


inline_for_extraction noextract
val make_g2: f:qelem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    qas_nat h1 f == SG.g2)

let make_g2 f =
  [@inline_let]
  let x =
   (u64 0x1571b4ae8ac47f71,
    u64 0x221208ac9df506c6,
    u64 0x6f547fa90abfe4c4,
    u64 0xe4437ed6010e8828) in

  assert_norm (SG.g2 == qas_nat4 x);
  make_u64_4 f x


(**
  Representing a scalar k as (r1 + r2 * lambda) mod S.q,
  s.t. r1 and r2 are ~128 bits long
*)

inline_for_extraction noextract
val scalar_split_lambda_g1g2 (tmp1 tmp2 r1 r2 k: qelem) : Stack unit
  (requires fun h ->
    live h k /\ live h r1 /\ live h r2 /\
    live h tmp1 /\ live h tmp2 /\
    disjoint k r1 /\ disjoint k r2 /\ disjoint r1 r2 /\
    disjoint tmp1 r1 /\ disjoint tmp1 r2 /\ disjoint tmp1 k /\
    disjoint tmp2 r1 /\ disjoint tmp2 r2 /\ disjoint tmp2 k /\
    disjoint tmp1 tmp2 /\ qas_nat h k < S.q)
  (ensures  fun h0 _ h1 ->
    modifies (loc r1 |+| loc r2 |+| loc tmp1 |+| loc tmp2) h0 h1 /\
   (let r1 = qas_nat h1 r1 in let r2 = qas_nat h1 r2 in
    r1 < S.q /\ r1 = SG.qmul_shift_384 (qas_nat h0 k) SG.g1 /\
    r2 < S.q /\ r2 = SG.qmul_shift_384 (qas_nat h0 k) SG.g2))

let scalar_split_lambda_g1g2 tmp1 tmp2 r1 r2 k =
  make_g1 tmp1; // tmp1 = g1
  make_g2 tmp2; // tmp2 = g2
  qmul_shift_384 r1 k tmp1; // r1 = c1 = qmul_shift_384 k g1
  qmul_shift_384 r2 k tmp2; // r2 = c2 = qmul_shift_384 k g2
  let h0 = ST.get () in
  SG.qmul_shift_384_lemma (qas_nat h0 k) (qas_nat h0 tmp1);
  SG.qmul_shift_384_lemma (qas_nat h0 k) (qas_nat h0 tmp2);
  assert (qas_nat h0 r1 < S.q /\ qas_nat h0 r2 < S.q)


// k = (r1 + lambda * k2) % S.q
val scalar_split_lambda (r1 r2 k: qelem) : Stack unit
  (requires fun h ->
    live h k /\ live h r1 /\ live h r2 /\
    disjoint k r1 /\ disjoint k r2 /\ disjoint r1 r2 /\
    qas_nat h k < S.q)
  (ensures  fun h0 _ h1 -> modifies (loc r1 |+| loc r2) h0 h1 /\
   (let r1_s, r2_s = SG.scalar_split_lambda (qas_nat h0 k) in
    qas_nat h1 r1 == r1_s /\ qas_nat h1 r2 == r2_s))

[@CInline]
let scalar_split_lambda r1 r2 k =
  push_frame ();
  let tmp1 = create_qelem () in
  let tmp2 = create_qelem () in
  scalar_split_lambda_g1g2 tmp1 tmp2 r1 r2 k;

  make_minus_b1 tmp1; // tmp1 = minus_b1
  make_minus_b2 tmp2; // tmp2 = minus_b2
  qmul r1 r1 tmp1; // r1 = c1 = c1 * minus_b1
  qmul r2 r2 tmp2; // r2 = c2 = c2 * minus_b2

  make_minus_lambda tmp1; // tmp1 = minus_lambda
  qadd r2 r1 r2; // r2 = r2 = c1 + c2
  qmul tmp2 r2 tmp1; // tmp2 = r2 * minus_lambda
  qadd r1 k tmp2; // r1 = r1 = k + r2 * minus_lambda
  pop_frame ()


(**
 Fast computation of [lambda]P as (beta * px, py, pz) in projective coordinates
*)

// [lambda]P = (beta * px, py, pz)
val point_mul_lambda: res:point -> p:point -> Stack unit
  (requires fun h ->
    live h res /\ live h p /\ eq_or_disjoint res p /\
    point_inv h p)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    point_inv h1 res /\
    point_eval h1 res == SG.point_mul_lambda (point_eval h0 p))

[@CInline]
let point_mul_lambda res p =
  push_frame ();
  let rx, ry, rz = getx res, gety res, getz res in
  let px, py, pz = getx p, gety p, getz p in
  let beta = create_felem () in
  make_beta beta;
  fmul rx beta px;

  copy_felem ry py;
  copy_felem rz pz;
  pop_frame ()


// [lambda]P = (beta * px, py, pz)
val point_mul_lambda_inplace: res:point -> Stack unit
  (requires fun h ->
    live h res /\ point_inv h res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    point_inv h1 res /\
    point_eval h1 res == SG.point_mul_lambda (point_eval h0 res))

[@CInline]
let point_mul_lambda_inplace res =
  push_frame ();
  let rx, ry, rz = getx res, gety res, getz res in
  let beta = create_felem () in
  make_beta beta;
  fmul rx beta rx;
  pop_frame ()


inline_for_extraction noextract
val point_mul_lambda_and_split_lambda:
  r1:qelem -> r2:qelem -> lambda_q:point -> scalar:qelem -> q:point -> Stack unit
  (requires fun h ->
    live h r1 /\ live h r2 /\ live h lambda_q /\ live h scalar /\ live h q /\
    disjoint r1 r2 /\ disjoint r1 lambda_q /\ disjoint r1 scalar /\ disjoint r1 q /\
    disjoint r2 lambda_q /\ disjoint r2 scalar /\ disjoint r2 q /\
    disjoint lambda_q scalar /\ disjoint lambda_q q /\
    point_inv h q /\ qas_nat h scalar < S.q)
  (ensures fun h0 _ h1 -> modifies (loc r1 |+| loc r2 |+| loc lambda_q) h0 h1 /\
    point_inv h1 lambda_q /\
    point_eval h1 lambda_q == SG.point_mul_lambda (point_eval h0 q) /\
   (let r1_s, r2_s = SG.scalar_split_lambda (qas_nat h0 scalar) in
    qas_nat h1 r1 == r1_s /\ qas_nat h1 r2 == r2_s))

let point_mul_lambda_and_split_lambda r1 r2 lambda_q scalar q =
  scalar_split_lambda r1 r2 scalar; // (r1 + r2 * lambda) % S.q = scalar
  point_mul_lambda lambda_q q // lambda_q = [lambda]Q


inline_for_extraction noextract
val point_negate_conditional_vartime: p:point -> is_negate:bool -> Stack unit
  (requires fun h -> live h p /\ point_inv h p)
  (ensures  fun h0 _ h1 -> modifies (loc p) h0 h1 /\
    point_inv h1 p /\
    point_eval h1 p == SG.point_negate_cond (point_eval h0 p) is_negate)

let point_negate_conditional_vartime p is_negate =
  if is_negate then point_negate p p


inline_for_extraction noextract
val negate_point_and_scalar_cond_vartime: k:qelem -> p:point -> Stack bool
  (requires fun h ->
    live h k /\ live h p /\ disjoint k p /\
    qas_nat h k < S.q /\ point_inv h p)
  (ensures  fun h0 b h1 -> modifies (loc k |+| loc p) h0 h1 /\
    b == S.scalar_is_high (qas_nat h0 k) /\ point_inv h1 p /\
    (let k_s, p_s = SG.negate_point_and_scalar_cond (qas_nat h0 k) (point_eval h0 p) in
    qas_nat h1 k == k_s /\ point_eval h1 p == p_s))

let negate_point_and_scalar_cond_vartime k p =
  let b = is_qelem_le_q_halved_vartime k in
  [@inline_let] let if_high = not b in
  qnegate_conditional_vartime k if_high;
  point_negate_conditional_vartime p if_high;
  if_high


inline_for_extraction noextract
val ecmult_endo_split:
    r1:qelem -> r2:qelem
  -> q1:point -> q2:point
  -> scalar:qelem -> q:point -> Stack (bool & bool)
  (requires fun h ->
    live h r1 /\ live h r2 /\ live h q1 /\
    live h q2 /\ live h scalar /\ live h q /\
    disjoint r1 r2 /\ disjoint r1 q1 /\ disjoint r1 q2 /\
    disjoint r1 scalar /\ disjoint r1 q /\ disjoint r2 q1 /\
    disjoint r2 q2 /\ disjoint r2 scalar /\ disjoint r2 q /\
    disjoint q1 q2 /\ disjoint q1 scalar /\ disjoint q1 q /\
    disjoint q2 scalar /\ disjoint q2 q /\
    point_inv h q /\ qas_nat h scalar < S.q)
  (ensures fun h0 (is_high1, is_high2) h1 ->
    modifies (loc r1 |+| loc r2 |+| loc q1 |+| loc q2) h0 h1 /\
    point_inv h1 q1 /\ point_inv h1 q2 /\
   (let r1_s0, r2_s0 = SG.scalar_split_lambda (qas_nat h0 scalar) in
    let r1_s, q1_s, r2_s, q2_s = SG.ecmult_endo_split (qas_nat h0 scalar) (point_eval h0 q) in
    qas_nat h1 r1 == r1_s /\ r1_s < pow2 128 /\
    qas_nat h1 r2 == r2_s /\ r2_s < pow2 128 /\
    point_eval h1 q1 == q1_s /\ point_eval h1 q2 == q2_s /\
    is_high1 == S.scalar_is_high r1_s0 /\
    is_high2 == S.scalar_is_high r2_s0))

let ecmult_endo_split r1 r2 q1 q2 scalar q =
  let h0 = ST.get () in
  // modifies r1, r2, q2 s.t. r1 + r2 * lambda = scalar /\ q2 = [lambda]q
  point_mul_lambda_and_split_lambda r1 r2 q2 scalar q;
  copy q1 q; // q1 = q
  // modifies r1, q1
  let is_high1 = negate_point_and_scalar_cond_vartime r1 q1 in
  // modifies r2, q2
  let is_high2 = negate_point_and_scalar_cond_vartime r2 q2 in
  SGL.lemma_scalar_split_lambda_fits (qas_nat h0 scalar) (point_eval h0 q);
  is_high1, is_high2
