module Hacl.Impl.PCurves.Constants.P256

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.PCurves.Bignum

module S = Spec.PCurves
module SM = Hacl.Spec.PCurves.Montgomery
module CC = Hacl.Impl.PCurves.Constants


open Spec.P256

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"
[@CInline]
val p256_make_prime: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n == S.prime)

[@CInline]
let p256_make_prime n =
    // 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
    [@inline_let] let n0 = u64 0xffffffffffffffff in
    [@inline_let] let n1 = u64 0xffffffff in
    [@inline_let] let n2 = u64 0x0 in
    [@inline_let] let n3 = u64 0xffffffff00000001 in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 = Spec.P256.p256_prime);
    bn_make_u64_4 n n0 n1 n2 n3

[@CInline]
val p256_make_order: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n == S.order)

[@CInline]
let p256_make_order n =
    // 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
    [@inline_let] let n0 = u64 0xf3b9cac2fc632551 in
    [@inline_let] let n1 = u64 0xbce6faada7179e84 in
    [@inline_let] let n2 = u64 0xffffffffffffffff in
    [@inline_let] let n3 = u64 0xffffffff00000000 in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 = Spec.P256.p256_order);
    bn_make_u64_4 n n0 n1 n2 n3

[@CInline]
val p256_make_a_coeff: a:felem -> Stack unit
  (requires fun h -> live h a)
  (ensures fun h0 _ h1 -> modifies (loc a) h0 h1 /\
    as_nat h1 a < S.prime /\
    SM.from_mont (as_nat h1 a) == S.a_coeff)

[@CInline]
let p256_make_a_coeff a =
    // a_coeff      = 0xffffffff00000001000000000000000000000000fffffffffffffffffffffffc
    // a_coeff_mont = 0xfffffffc00000004000000000000000000000003fffffffffffffffffffffffc
    [@inline_let] let n0 = u64 0xfffffffffffffffc in
    [@inline_let] let n1 = u64 0x3ffffffff in
    [@inline_let] let n2 = u64 0x0 in
    [@inline_let] let n3 = u64 0xfffffffc00000004 in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 < S.prime);
    assert (SM.to_mont #p256_params p256_a_coeff == p256_a_coeff * pow2 (64 * 4) % p256_prime);
    assert_norm (p256_a_coeff * pow2 (64 * 4) % p256_prime == v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192);
    SM.lemma_to_from_mont_id S.a_coeff;
    bn_make_u64_4 a n0 n1 n2 n3

[@CInline]
val p256_make_b_coeff: b:felem -> Stack unit
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    as_nat h1 b < S.prime /\
    SM.from_mont (as_nat h1 b) == S.b_coeff)

[@CInline]
let p256_make_b_coeff b =
    // b_coeff      = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
    // b_coeff_mont = 0xdc30061d04874834e5a220abf7212ed6acf005cd78843090d89cdf6229c4bddf
    [@inline_let] let n0 = u64 0xd89cdf6229c4bddf in
    [@inline_let] let n1 = u64 0xacf005cd78843090 in
    [@inline_let] let n2 = u64 0xe5a220abf7212ed6 in
    [@inline_let] let n3 = u64 0xdc30061d04874834 in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 < S.prime);
    assert (SM.to_mont #p256_params p256_b_coeff == p256_b_coeff * pow2 (64 * 4) % p256_prime);
    assert_norm (p256_b_coeff * pow2 (64 * 4) % p256_prime == v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192);
    SM.lemma_to_from_mont_id S.b_coeff;
    bn_make_u64_4 b n0 n1 n2 n3


[@CInline]
val p256_make_g_x: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n < S.prime /\
    SM.from_mont (as_nat h1 n) == S.basepoint_x)

[@CInline]
let p256_make_g_x n =
    // g_x = 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
    // mont_g_x = 0x18905f76a53755c679fb732b7762251075ba95fc5fedb60179e730d418a9143c
    [@inline_let] let n0 = u64 0x79e730d418a9143c in
    [@inline_let] let n1 = u64 0x75ba95fc5fedb601 in
    [@inline_let] let n2 = u64 0x79fb732b77622510 in
    [@inline_let] let n3 = u64 0x18905f76a53755c6 in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 < S.prime);
    assert (SM.to_mont #p256_params p256_basepoint_x == p256_basepoint_x * pow2 (64 * 4) % p256_prime);
    assert_norm (p256_basepoint_x * pow2 (64 * 4) % p256_prime == v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192);
    SM.lemma_to_from_mont_id S.basepoint_x;
    bn_make_u64_4 n n0 n1 n2 n3

[@CInline]
val p256_make_g_y: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n < S.prime /\
    SM.from_mont (as_nat h1 n) == S.basepoint_y)

[@CInline]
let p256_make_g_y n =
    // g_y = 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5
    // mont_g_x = 0x8571ff1825885d85d2e88688dd21f3258b4ab8e4ba19e45cddf25357ce95560a
    [@inline_let] let n0 = u64 0xddf25357ce95560a in
    [@inline_let] let n1 = u64 0x8b4ab8e4ba19e45c in
    [@inline_let] let n2 = u64 0xd2e88688dd21f325 in
    [@inline_let] let n3 = u64 0x8571ff1825885d85 in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 < S.prime);
    assert (SM.to_mont #p256_params p256_basepoint_y == p256_basepoint_y * pow2 (64 * 4) % p256_prime);
    assert_norm (p256_basepoint_y * pow2 (64 * 4) % p256_prime == v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192);
    SM.lemma_to_from_mont_id S.basepoint_y;
    bn_make_u64_4 n n0 n1 n2 n3

[@CInline]
val p256_make_fmont_R2: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n == SM.fmont_R * SM.fmont_R % S.prime)

[@CInline]
let p256_make_fmont_R2 n =
    // 0x4fffffffdfffffffffffffffefffffffbffffffff0000000000000003
    [@inline_let] let n0 = u64 0x3 in
    [@inline_let] let n1 = u64 0xfffffffbffffffff in
    [@inline_let] let n2 = u64 0xfffffffffffffffe in
    [@inline_let] let n3 = u64 0x4fffffffd in
    assert (SM.fmont_R * SM.fmont_R % S.prime == pow2 (64 * 4) * pow2 (64 * 4)  % p256_prime);
    assert_norm (pow2 (64 * 4) * pow2 (64 * 4) % p256_prime == v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192);
    bn_make_u64_4 n n0 n1 n2 n3

[@CInline]
val p256_make_fzero: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n < S.prime /\
    CC.fmont_as_nat h1 n == 0)

[@CInline]
let p256_make_fzero n =
  bn_set_zero n;
  assert_norm (SM.to_mont 0 = 0);
  SM.lemma_to_from_mont_id 0


[@CInline]
val p256_make_fone: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n < S.prime /\
    CC.fmont_as_nat h1 n == 1)
[@CInline]
let p256_make_fone n =
    // 0xfffffffeffffffffffffffffffffffff000000000000000000000001
    [@inline_let] let n0 = u64 0x1 in
    [@inline_let] let n1 = u64 0xffffffff00000000 in
    [@inline_let] let n2 = u64 0xffffffffffffffff in
    [@inline_let] let n3 = u64 0xfffffffe in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 < S.prime);
    assert (SM.to_mont #p256_params 1 == pow2 (64 * 4) % p256_prime);
    assert_norm (pow2 (64 * 4) % p256_prime == v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192);
    SM.lemma_to_from_mont_id 1;
    bn_make_u64_4 n n0 n1 n2 n3


[@CInline]
val p256_make_qone: f:felem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    as_nat h1 f < S.order /\
    CC.qmont_as_nat h1 f == 1)

[@CInline]
let p256_make_qone f =
    [@inline_let] let f0 = u64 0xc46353d039cdaaf in
    [@inline_let] let f1 = u64 0x4319055258e8617b in
    [@inline_let] let f2 = u64 0x0 in
    [@inline_let] let f3 = u64 0xffffffff in
    assert_norm (v f0 + v f1 * pow2 64 + v f2 * pow2 128 + v f3 * pow2 192 < S.order);
    assert (SM.to_qmont #p256_params 1 == pow2 (64 * 4) % p256_order);
    assert_norm (pow2 (64 * 4) % p256_order == v f0 + v f1 * pow2 64 + v f2 * pow2 128 + v f3 * pow2 192);
    SM.lemma_to_from_qmont_id 1;
    bn_make_u64_4 f f0 f1 f2 f3


inline_for_extraction
instance p256_curve_constants : CC.curve_constants = {
  make_prime = p256_make_prime;
  make_order = p256_make_order;
  make_a_coeff = p256_make_a_coeff;
  make_b_coeff = p256_make_b_coeff;
  make_g_x = p256_make_g_x;
  make_g_y = p256_make_g_y;
  make_fmont_R2 = p256_make_fmont_R2;
  make_fzero = p256_make_fzero;
  make_fone = p256_make_fone;
  make_qone = p256_make_qone
}

