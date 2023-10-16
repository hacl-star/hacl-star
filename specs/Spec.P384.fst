module Spec.P384
open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.PCurves

///  P-384 Curve Parameters

inline_for_extraction noextract
let p384_bits = 384

inline_for_extraction noextract
let p384_bytes : (x:nat{8 * x >= p384_bits}) = 48


// Prime  0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff
inline_for_extraction noextract
let p384_prime: (a:pos{a = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff /\ a < pow2 384}) =
  let p = pow2 384 - pow2 128 - pow2 96 + pow2 32 - 1 in
  assert_norm (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff = p);
  assert_norm (p < pow2 384); p

inline_for_extraction noextract
let p384_order: (a:pos{a < pow2 384}) =
  let o = 0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973 in
  assert_norm (o < pow2 384); o

inline_for_extraction noextract
let p384_a_coeff : (x:pos{x < p384_prime}) = (-3) % p384_prime
let p384_b_coeff : (x:pos{x < p384_prime}) =
  let b = 0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef in
  assert_norm (b < p384_prime); b

inline_for_extraction noextract
let p384_basepoint_x : (x:pos{x < p384_prime}) =
  let x = 0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7 in
  assert_norm (x < p384_prime); x

inline_for_extraction noextract
let p384_basepoint_y : (x:pos{x < p384_prime}) =
  let y = 0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f in
  assert_norm (y < p384_prime); y

inline_for_extraction noextract
let p384_mont_mu: (x:uint64{(1 + p384_prime * v x) % pow2 64 == 0}) =
  assert_norm((1 + p384_prime * 4294967297) % pow2 64 == 0);
  u64 4294967297

inline_for_extraction noextract
let p384_mont_q_mu: (x:uint64{(1 + p384_order * v x) % pow2 64 == 0}) =
  assert_norm((1 + p384_order * 7986114184663260229) % pow2 64 == 0);
  u64 7986114184663260229

inline_for_extraction noextract
let p384_bn_limbs: (x:size_t{v x = (p384_bytes + 7) / 8}) =
  assert_norm(6 == (p384_bytes + 7) / 8);
  size 6

inline_for_extraction noextract
instance p384_params : curve_params = {
  bits = p384_bits;
  bytes = p384_bytes;
  size_bytes = 48ul;
  prime = p384_prime;
  order = p384_order;
  basepoint_x = p384_basepoint_x;
  basepoint_y = p384_basepoint_y;
  a_coeff = p384_a_coeff;
  b_coeff = p384_b_coeff;
  mont_mu = p384_mont_mu;
  mont_q_mu = p384_mont_q_mu;
  bn_limbs = p384_bn_limbs
}

let p384_basepoint : proj_point #p384_params =
  (p384_basepoint_x,p384_basepoint_y,one)
