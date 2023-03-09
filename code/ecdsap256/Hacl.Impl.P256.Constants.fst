module Hacl.Impl.P256.Constants

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Felem
open Hacl.Impl.P256.Bignum

module S = Spec.P256
module SM = Hacl.Spec.P256.MontgomeryMultiplication

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val make_prime: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n == S.prime)

[@CInline]
let make_prime n =
  // 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
  [@inline_let] let n0 = u64 0xffffffffffffffff in
  [@inline_let] let n1 = u64 0xffffffff in
  [@inline_let] let n2 = u64 0x0 in
  [@inline_let] let n3 = u64 0xffffffff00000001 in
  assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 = S.prime);
  bn_make_u64_4 n0 n1 n2 n3 n


val make_order: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n == S.order)

[@CInline]
let make_order n =
  // 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
  [@inline_let] let n0 = u64 0xf3b9cac2fc632551 in
  [@inline_let] let n1 = u64 0xbce6faada7179e84 in
  [@inline_let] let n2 = u64 0xffffffffffffffff in
  [@inline_let] let n3 = u64 0xffffffff00000000 in
  assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 = S.order);
  bn_make_u64_4 n0 n1 n2 n3 n


val make_a_coeff: a:felem -> Stack unit
  (requires fun h -> live h a)
  (ensures fun h0 _ h1 -> modifies (loc a) h0 h1 /\
    as_nat h1 a == SM.toDomain_ S.a_coeff /\
    SM.fromDomain_ (as_nat h1 a) == S.a_coeff /\
    as_nat h1 a < S.prime)

[@CInline]
let make_a_coeff a =
  // a_coeff      = 0xffffffff00000001000000000000000000000000fffffffffffffffffffffffc
  // a_coeff_mont = 0xfffffffc00000004000000000000000000000003fffffffffffffffffffffffc
  [@inline_let] let n0 = u64 0xfffffffffffffffc in
  [@inline_let] let n1 = u64 0x3ffffffff in
  [@inline_let] let n2 = u64 0x0 in
  [@inline_let] let n3 = u64 0xfffffffc00000004 in
  assert_norm (
    v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 == SM.toDomain_ S.a_coeff);
  assert_norm (
    SM.fromDomain_ (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192) == S.a_coeff);
  bn_make_u64_4 n0 n1 n2 n3 a


val make_b_coeff: b:felem -> Stack unit
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    as_nat h1 b == SM.toDomain_ S.b_coeff /\
    SM.fromDomain_ (as_nat h1 b) == S.b_coeff /\
    as_nat h1 b < S.prime)

[@CInline]
let make_b_coeff b =
  // b_coeff      = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
  // b_coeff_mont = 0xdc30061d04874834e5a220abf7212ed6acf005cd78843090d89cdf6229c4bddf
  [@inline_let] let n0 = u64 0xd89cdf6229c4bddf in
  [@inline_let] let n1 = u64 0xacf005cd78843090 in
  [@inline_let] let n2 = u64 0xe5a220abf7212ed6 in
  [@inline_let] let n3 = u64 0xdc30061d04874834 in
  assert_norm (
    v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 == SM.toDomain_ S.b_coeff);
  assert_norm (
    SM.fromDomain_ (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192) == S.b_coeff);
  bn_make_u64_4 n0 n1 n2 n3 b


val make_g_x: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n == SM.toDomain_ S.g_x /\
    SM.fromDomain_ (as_nat h1 n) == S.g_x)

[@CInline]
let make_g_x n =
  // g_x = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
  // mont_g_x = 0x18905f76a53755c679fb732b7762251075ba95fc5fedb60179e730d418a9143c
  [@inline_let] let n0 = u64 0x79e730d418a9143c in
  [@inline_let] let n1 = u64 0x75ba95fc5fedb601 in
  [@inline_let] let n2 = u64 0x79fb732b77622510 in
  [@inline_let] let n3 = u64 0x18905f76a53755c6 in
  assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 == SM.toDomain_ S.g_x);
  assert_norm (SM.fromDomain_ (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192) == S.g_x);
  bn_make_u64_4 n0 n1 n2 n3 n


val make_g_y: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n == SM.toDomain_ S.g_y /\
    SM.fromDomain_ (as_nat h1 n) == S.g_y)

[@CInline]
let make_g_y n =
  // g_y = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5
  // mont_g_x = 0x8571ff1825885d85d2e88688dd21f3258b4ab8e4ba19e45cddf25357ce95560a
  [@inline_let] let n0 = u64 0xddf25357ce95560a in
  [@inline_let] let n1 = u64 0x8b4ab8e4ba19e45c in
  [@inline_let] let n2 = u64 0xd2e88688dd21f325 in
  [@inline_let] let n3 = u64 0x8571ff1825885d85 in
  assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 == SM.toDomain_ S.g_y);
  assert_norm (SM.fromDomain_ (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192) == S.g_y);
  bn_make_u64_4 n0 n1 n2 n3 n
