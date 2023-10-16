module Spec.P521
open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.PCurves

///  P-521 Curve Parameters

inline_for_extraction noextract
let p521_bits = 521

inline_for_extraction noextract
let p521_bytes : (x:nat{8 * x >= p521_bits}) = 66


// Prime  0x01ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
inline_for_extraction noextract
let p521_prime: (a:pos{a = 0x01ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff /\ a < pow2 521}) =
  let p = pow2 521 - 1 in
  assert_norm (p < pow2 521); 
  assert_norm (0x01ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff = p);
  p

inline_for_extraction noextract
let p521_order: (a:pos{a < pow2 521}) =
  let o = 0x01fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa51868783bf2f966b7fcc0148f709a5d03bb5c9b8899c47aebb6fb71e91386409 in
  assert_norm (o < pow2 521); o

// 0x01fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc
inline_for_extraction noextract
let p521_a_coeff : (x:pos{x < p521_prime}) = (-3) % p521_prime
let p521_b_coeff : (x:pos{x < p521_prime}) =
  let b =  0x0051953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef109e156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd46b503f00 in
  assert_norm (b < p521_prime); b

inline_for_extraction noextract
let p521_basepoint_x : (x:pos{x < p521_prime}) =
  let x = 0x00c6858e06b70404e9cd9e3ecb662395b4429c648139053fb521f828af606b4d3dbaa14b5e77efe75928fe1dc127a2ffa8de3348b3c1856a429bf97e7e31c2e5bd66 in
  assert_norm (x < p521_prime); x

inline_for_extraction noextract
let p521_basepoint_y : (x:pos{x < p521_prime}) =
  let y = 0x011839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e662c97ee72995ef42640c550b9013fad0761353c7086a272c24088be94769fd16650 in
  assert_norm (y < p521_prime); y

inline_for_extraction noextract
let p521_mont_mu: (x:uint64{(1 + p521_prime * v x) % pow2 64 == 0}) =
  assert_norm((1 + p521_prime) % pow2 64 == 0);
  u64 1

inline_for_extraction noextract
let p521_mont_q_mu: (x:uint64{(1 + p521_order * v x) % pow2 64 == 0}) =
  assert_norm((1 + p521_order * 2103001588584519111) % pow2 64 == 0);
  u64 2103001588584519111

inline_for_extraction noextract
let p521_bn_limbs: (x:size_t{v x = (p521_bytes + 7) / 8}) =
  assert_norm(9 == (p521_bytes + 7) / 8);
  size 9

inline_for_extraction noextract
instance p521_params : curve_params = {
  bits = p521_bits;
  bytes = p521_bytes;
  size_bytes = 66ul;
  prime = p521_prime;
  order = p521_order;
  basepoint_x = p521_basepoint_x;
  basepoint_y = p521_basepoint_y;
  a_coeff = p521_a_coeff;
  b_coeff = p521_b_coeff;
  mont_mu = p521_mont_mu;
  mont_q_mu = p521_mont_q_mu;
  bn_limbs = p521_bn_limbs
}

let p521_basepoint : proj_point #p521_params =
  (p521_basepoint_x,p521_basepoint_y,one)
