module Spec.K256.PointOps

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

module BSeq = Lib.ByteSequence
module EC = Spec.EC.Projective

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

let prime : (p:pos{p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F}) =
  assert_norm (24 < pow2 256 - 0x1000003D1);
  assert_norm (pow2 256 - 0x1000003D1 = pow2 256 - pow2 32 - pow2 9 - pow2 8 - pow2 7 - pow2 6 - pow2 4 - 1);
  assert_norm (pow2 256 - 0x1000003D1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F);
  pow2 256 - 0x1000003D1

// Group order
let q : q:pos{q < pow2 256} =
  assert_norm (0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 < pow2 256);
  0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141


let felem = x:nat{x < prime}
let qelem = x:nat{x < q}

let a : felem = 0
let b : felem = 7

// Base point
let g_x : felem = 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798
let g_y : felem = 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8


assume
val prime_lemma: unit -> Lemma (FStar.Math.Euclid.is_prime prime)

assume
val order_lemma: unit -> Lemma (FStar.Math.Euclid.is_prime q)

val weierstrass_curve: unit ->
  Lemma ((4 * a * a * a + 27 * b * b) % prime <> 0)

let weierstrass_curve () =
  assert_norm ((4 * a * a * a + 27 * b * b) % prime <> 0)


let k256: EC.curve = {
  EC.prime = prime;
  EC.coeff_a = a;
  EC.coeff_b = b;

  EC.order = q;
  EC.base_point = (g_x, g_y);

  EC.prime_len_bytes = 32;
  EC.order_len_bytes = 32;

  EC.weierstrass_curve;
  EC.prime_lemma;
  EC.order_lemma;
}


///  Point conversion between affine, projective and bytes representation

let point_inv_bytes (b:BSeq.lbytes 64) =
  let px = BSeq.nat_from_bytes_be (sub b 0 32) in
  let py = BSeq.nat_from_bytes_be (sub b 32 32) in
  px < prime && py < prime && EC.is_on_curve k256 (px, py)

let load_point_nocheck (b:BSeq.lbytes 64{point_inv_bytes b}) : EC.proj_point k256 =
  let px = BSeq.nat_from_bytes_be (sub b 0 32) in
  let py = BSeq.nat_from_bytes_be (sub b 32 32) in
  EC.to_proj_point k256 (px, py)
