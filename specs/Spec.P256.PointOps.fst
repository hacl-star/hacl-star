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
