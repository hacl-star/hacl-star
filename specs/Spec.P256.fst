module Spec.P256
open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.PCurves

///  P-256 Curve Parameters

inline_for_extraction noextract
let p256_bits = 256

inline_for_extraction noextract
let p256_bytes : (x:nat{8 * x >= p256_bits}) = 32

inline_for_extraction noextract
let p256_prime: (a:pos{a = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff /\ a < pow2 256}) =
  let p = pow2 256 - pow2 224 + pow2 192 + pow2 96 - 1 in
  assert_norm (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff = p);
  assert_norm (p < pow2 256); p

inline_for_extraction noextract
let p256_order: (a:pos{a < pow2 256}) =
  let o = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551 in
  assert_norm (o < pow2 256); o

inline_for_extraction noextract
let p256_a_coeff : (x:pos{x < p256_prime}) = (-3) % p256_prime
let p256_b_coeff : (x:pos{x < p256_prime}) =
  let b = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b in
  assert_norm (b < p256_prime); b

inline_for_extraction noextract
let p256_basepoint_x : (x:pos{x < p256_prime}) =
  let x = 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296 in
  assert_norm (x < p256_prime); x
inline_for_extraction noextract
let p256_basepoint_y : (x:pos{x < p256_prime}) =
  let y = 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5 in
  assert_norm (y < p256_prime); y

inline_for_extraction noextract
let p256_mont_mu: (x:uint64{(1 + p256_prime * v x) % pow2 64 == 0}) =
  assert_norm((1 + p256_prime) % pow2 64 == 0);
  u64 1

inline_for_extraction noextract
let p256_mont_q_mu: (x:uint64{(1 + p256_order * v x) % pow2 64 == 0}) =
  assert_norm((1 + p256_order * 0xccd1c8aaee00bc4f) % pow2 64 == 0);
  u64 0xccd1c8aaee00bc4f

inline_for_extraction noextract
let p256_bn_limbs: (x:size_t{v x = (p256_bytes + 7) / 8}) =
  assert_norm(4 == (p256_bytes + 7) / 8);
  size 4

inline_for_extraction noextract
instance p256_params : curve_params = {
  bits = p256_bits;
  bytes = p256_bytes;
  size_bytes = 32ul;
  prime = p256_prime;
  order = p256_order;
  basepoint_x = p256_basepoint_x;
  basepoint_y = p256_basepoint_y;
  a_coeff = p256_a_coeff;
  b_coeff = p256_b_coeff;
  mont_mu = p256_mont_mu;
  mont_q_mu = p256_mont_q_mu;
  bn_limbs = p256_bn_limbs
}

let p256_basepoint = base_point
