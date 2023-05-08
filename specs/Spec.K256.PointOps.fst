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


let ( +% ) = EC.fadd k256
let ( -% ) = EC.fsub k256
let ( *% ) = EC.fmul k256
let ( /% ) (x y:felem) = EC.fmul k256 x (EC.finv k256 y)


///  Point addition in affine coordinates

let aff_point_negate (p:EC.aff_point k256) : EC.aff_point k256 =
  let x, y = p in x, (-y) % prime


///  Point addition and doubling in projective coordinates

let point_add (p:EC.proj_point k256) (q:EC.proj_point k256) : EC.proj_point k256 =
  let x1, y1, z1 = p in
  let x2, y2, z2 = q in
  let xx = x1 *% x2 in
  let yy = y1 *% y2 in
  let zz = z1 *% z2 in
  let xy_pairs = (x1 +% y1) *% (x2 +% y2) -% (xx +% yy) in
  let yz_pairs = (y1 +% z1) *% (y2 +% z2) -% (yy +% zz) in
  let xz_pairs = (x1 +% z1) *% (x2 +% z2) -% (xx +% zz) in
  let bzz3 = 3 *% b *% zz in
  let yy_m_bzz3 = yy -% bzz3 in
  let yy_p_bzz3 = yy +% bzz3 in
  let byz3 = 3 *% b *% yz_pairs in
  let xx3 = 3 *% xx in
  let bxx9 = 3 *% b *% xx3 in
  let x3 = xy_pairs *% yy_m_bzz3 -% byz3 *% xz_pairs in
  let y3 = yy_p_bzz3 *% yy_m_bzz3 +% bxx9 *% xz_pairs in
  let z3 = yz_pairs *% yy_p_bzz3 +% xx3 *% xy_pairs in
  x3, y3, z3

let point_double (p:EC.proj_point k256) : EC.proj_point k256 =
  let x, y, z = p in
  let yy = y *% y in
  let zz = z *% z in
  let xy2 = 2 *% x *% y in
  let bzz3 = 3 *% b *% zz in
  let bzz9 = 3 *% bzz3 in
  let yy_m_bzz9 = yy -% bzz9 in
  let yy_p_bzz3 = yy +% bzz3 in
  let yy_zz = yy *% zz in
  let t = 24 *% b *% yy_zz in
  let x3 = xy2 *% yy_m_bzz9 in
  let y3 = yy_m_bzz9 *% yy_p_bzz3 +% t in
  let z3 = yy *% y *% z *% 8 in
  x3, y3, z3

let point_negate (p:EC.proj_point k256) : EC.proj_point k256 =
  let x, y, z = p in
  x, (-y) % prime, z

///  Point conversion between affine, projective and bytes representation

let point_inv_bytes (b:BSeq.lbytes 64) =
  let px = BSeq.nat_from_bytes_be (sub b 0 32) in
  let py = BSeq.nat_from_bytes_be (sub b 32 32) in
  px < prime && py < prime && EC.is_on_curve k256 (px, py)

let load_point_nocheck (b:BSeq.lbytes 64{point_inv_bytes b}) : EC.proj_point k256 =
  let px = BSeq.nat_from_bytes_be (sub b 0 32) in
  let py = BSeq.nat_from_bytes_be (sub b 32 32) in
  EC.to_proj_point k256 (px, py)
