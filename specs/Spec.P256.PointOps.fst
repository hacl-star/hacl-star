module Spec.P256.PointOps

open FStar.Mul

module EC = Spec.EC.Projective

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

// 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
let prime: (a:pos{a = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff /\ a < pow2 256}) =
  let p = pow2 256 - pow2 224 + pow2 192 + pow2 96 - 1 in
  assert_norm (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff = p);
  assert_norm (p < pow2 256); p

let order: (a:pos{a < pow2 256}) =
  let o = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551 in
  assert_norm (o < pow2 256); o

let felem = x:nat{x < prime}
let qelem = x:nat{x < order}

let a_coeff : felem = (-3) % prime
let b_coeff : felem =
  let b = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b in
  assert_norm (b < prime); b

// Base point
let g_x : felem =
  let x = 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296 in
  assert_norm (x < prime); x
let g_y : felem =
  let y = 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5 in
  assert_norm (y < prime); y

assume
val prime_lemma: unit -> Lemma (FStar.Math.Euclid.is_prime prime)

assume
val order_lemma: unit -> Lemma (FStar.Math.Euclid.is_prime order)

val weierstrass_curve: unit ->
  Lemma ((4 * a_coeff * a_coeff * a_coeff + 27 * b_coeff * b_coeff) % prime <> 0)

let weierstrass_curve () =
  assert_norm ((4 * a_coeff * a_coeff * a_coeff + 27 * b_coeff * b_coeff) % prime <> 0)


let p256: EC.curve = {
  EC.prime = prime;
  EC.coeff_a = a_coeff;
  EC.coeff_b = b_coeff;

  EC.order = order;
  EC.base_point = (g_x, g_y);

  EC.prime_len_bytes = 32;
  EC.order_len_bytes = 32;

  EC.weierstrass_curve;
  EC.prime_lemma;
  EC.order_lemma;
}

let ( +% ) = EC.fadd p256
let ( -% ) = EC.fsub p256
let ( *% ) = EC.fmul p256

///  Point addition and doubling in projective coordinates

// Alg 4 from https://eprint.iacr.org/2015/1060.pdf
let point_add (p q:EC.proj_point p256) : EC.proj_point p256 =
  let x1, y1, z1 = p in
  let x2, y2, z2 = q in
  let t0 = x1 *% x2 in
  let t1 = y1 *% y2 in
  let t2 = z1 *% z2 in
  let t3 = x1 +% y1 in
  let t4 = x2 +% y2 in
  let t3 = t3 *% t4 in
  let t4 = t0 +% t1 in
  let t3 = t3 -% t4 in
  let t4 = y1 +% z1 in
  let t5 = y2 +% z2 in
  let t4 = t4 *% t5 in
  let t5 = t1 +% t2 in
  let t4 = t4 -% t5 in
  let x3 = x1 +% z1 in
  let y3 = x2 +% z2 in
  let x3 = x3 *% y3 in
  let y3 = t0 +% t2 in
  let y3 = x3 -% y3 in
  let z3 = b_coeff *% t2 in
  let x3 = y3 -% z3 in
  let z3 = x3 +% x3 in
  let x3 = x3 +% z3 in
  let z3 = t1 -% x3 in
  let x3 = t1 +% x3 in
  let y3 = b_coeff *% y3 in
  let t1 = t2 +% t2 in
  let t2 = t1 +% t2 in
  let y3 = y3 -% t2 in
  let y3 = y3 -% t0 in
  let t1 = y3 +% y3 in
  let y3 = t1 +% y3 in
  let t1 = t0 +% t0 in
  let t0 = t1 +% t0 in
  let t0 = t0 -% t2 in
  let t1 = t4 *% y3 in
  let t2 = t0 *% y3 in
  let y3 = x3 *% z3 in
  let y3 = y3 +% t2 in
  let x3 = t3 *% x3 in
  let x3 = x3 -% t1 in
  let z3 = t4 *% z3 in
  let t1 = t3 *% t0 in
  let z3 = z3 +% t1 in
  (x3, y3, z3)


// Alg 6 from https://eprint.iacr.org/2015/1060.pdf
let point_double (p:EC.proj_point p256) : EC.proj_point p256 =
  let (x, y, z) = p in
  let t0 = x *% x in
  let t1 = y *% y in
  let t2 = z *% z in
  let t3 = x *% y in
  let t3 = t3 +% t3 in
  let t4 = y *% z in
  let z3 = x *% z in
  let z3 = z3 +% z3 in
  let y3 = b_coeff *% t2 in
  let y3 = y3 -% z3 in
  let x3 = y3 +% y3 in
  let y3 = x3 +% y3 in
  let x3 = t1 -% y3 in
  let y3 = t1 +% y3 in
  let y3 = x3 *% y3 in
  let x3 = x3 *% t3 in
  let t3 = t2 +% t2 in
  let t2 = t2 +% t3 in
  let z3 = b_coeff *% z3 in
  let z3 = z3 -% t2 in
  let z3 = z3 -% t0 in
  let t3 = z3 +% z3 in
  let z3 = z3 +% t3 in
  let t3 = t0 +% t0 in
  let t0 = t3 +% t0 in
  let t0 = t0 -% t2 in
  let t0 = t0 *% z3 in
  let y3 = y3 +% t0 in
  let t0 = t4 +% t4 in
  let z3 = t0 *% z3 in
  let x3 = x3 -% z3 in
  let z3 = t0 *% t1 in
  let z3 = z3 +% z3 in
  let z3 = z3 +% z3 in
  (x3, y3, z3)
