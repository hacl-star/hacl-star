module Hacl.Spec.P256.Math

open FStar.Mul
open Spec.P256

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val mod_sub: n:pos -> a:int -> b:int -> Lemma
  (requires a % n = b % n)
  (ensures  (a - b) % n = 0)
let mod_sub n a b =
  Math.Lemmas.mod_add_both a b (-b) n


val sub_mod: n:pos -> a:int -> b:int -> Lemma
  (requires (a - b) % n = 0)
  (ensures  a % n = b % n)
let sub_mod n a b =
  Math.Lemmas.mod_add_both (a - b) 0 b n


val lemma_modular_multiplication_pow256: a:int -> b:int -> Lemma
  (requires a * pow2 256 % prime = b * pow2 256 % prime)
  (ensures  a % prime == b % prime)

let lemma_modular_multiplication_pow256 a b =
  mod_sub prime (a * pow2 256) (b * pow2 256);
  assert (pow2 256 * (a - b) % prime = 0);
  let r = 26959946654596436323893653559348051827142583427821597254581997273087 in
  let s = -26959946648319334592891477706824406424704094582978235142356758167551 in
  assert_norm (r * prime + s * pow2 256 = 1);
  FStar.Math.Euclid.euclid prime (pow2 256) (a - b) r s;
  assert ((a - b) % prime = 0);
  sub_mod prime a b;
  assert (a % prime = b % prime)


val lemma_modular_multiplication_p256_2_left:
  a:nat{a < prime} -> b:nat{b < prime} -> Lemma
  (requires a * pow2 256 % prime = b * pow2 256 % prime)
  (ensures  a == b)

let lemma_modular_multiplication_p256_2_left a b =
  lemma_modular_multiplication_pow256 a b;
  FStar.Math.Lemmas.modulo_lemma a prime;
  FStar.Math.Lemmas.modulo_lemma b prime


// used in Hacl.Impl.P256.Point
val lemma_modular_multiplication_p256_2: a: nat{a < prime} -> b: nat{b < prime} ->
  Lemma (a * pow2 256 % prime = b * pow2 256 % prime <==> a == b)

let lemma_modular_multiplication_p256_2 a b =
  Classical.move_requires_2 lemma_modular_multiplication_p256_2_left a b


// used in Hacl.Impl.P256.Scalar and Hacl.Impl.P256.Field
val lemma_montgomery_mod_inverse_addition: a:nat -> Lemma (
  a * modp_inv2_prime (pow2 64) prime * modp_inv2_prime (pow2 64) prime % prime ==
  a * modp_inv2_prime (pow2 128) prime % prime)

let lemma_montgomery_mod_inverse_addition a =
  calc (==) {
    a * modp_inv2_prime (pow2 64) prime * modp_inv2_prime (pow2 64) prime % prime;
    == { FStar.Math.Lemmas.paren_mul_right a (modp_inv2_prime (pow2 64) prime) (modp_inv2_prime (pow2 64) prime)}
    a * (modp_inv2_prime (pow2 64) prime * modp_inv2_prime (pow2 64) prime) % prime;
    == { FStar.Math.Lemmas.lemma_mod_mul_distr_r a
    (modp_inv2_prime (pow2 64) prime * modp_inv2_prime (pow2 64) prime) prime }
    a * (modp_inv2_prime (pow2 64) prime * modp_inv2_prime (pow2 64) prime % prime) % prime;
    == { assert_norm (modp_inv2_prime (pow2 64) prime * modp_inv2_prime (pow2 64) prime % prime ==
    modp_inv2_prime (pow2 128) prime % prime) }
    a * (modp_inv2_prime (pow2 128) prime % prime) % prime;
    == { FStar.Math.Lemmas.lemma_mod_mul_distr_r a (modp_inv2_prime (pow2 128) prime) prime }
    a * modp_inv2_prime (pow2 128) prime % prime;
  }


// used in Hacl.Impl.P256.Scalar and Hacl.Impl.P256.Field
val lemma_montgomery_mod_inverse_addition2: a:nat -> Lemma (
  a * modp_inv2_prime (pow2 128) prime * modp_inv2_prime (pow2 128) prime % prime ==
  a * modp_inv2_prime (pow2 256) prime % prime)

let lemma_montgomery_mod_inverse_addition2 a =
  calc (==) {
    a * modp_inv2_prime (pow2 128) prime * modp_inv2_prime (pow2 128) prime % prime;
    == { FStar.Math.Lemmas.paren_mul_right a (modp_inv2_prime (pow2 128) prime) (modp_inv2_prime (pow2 128) prime)}
    a * (modp_inv2_prime (pow2 128) prime * modp_inv2_prime (pow2 128) prime) % prime;
    == { FStar.Math.Lemmas.lemma_mod_mul_distr_r a
    (modp_inv2_prime (pow2 128) prime * modp_inv2_prime (pow2 128) prime) prime }
    a * (modp_inv2_prime (pow2 128) prime * modp_inv2_prime (pow2 128) prime % prime) % prime;
    == { assert_norm (modp_inv2_prime (pow2 128) prime * modp_inv2_prime (pow2 128) prime % prime ==
    modp_inv2_prime (pow2 256) prime % prime) }
    a * (modp_inv2_prime (pow2 256) prime % prime) % prime;
    == { FStar.Math.Lemmas.lemma_mod_mul_distr_r a (modp_inv2_prime (pow2 256) prime) prime }
    a * modp_inv2_prime (pow2 256) prime % prime;
  }

(* Fermat's Little Theorem
   applied to r = modp_inv2_prime (pow2 256) order

  Verified in Sage:
   prime = Zmod(Integer(115792089210356248762697446949407573530086143415290314195533631308867097853951))
   p = 41058363725152142129326129780047268409114441015993725554835256314039467401291
   C = EllipticCurve(prime, [-3, p])
   order =/ C.cardinality()
   Z = Integers(order)
   r = Z(inverse_mod(2**256, order))
   r ^ (order - 1)
*)
// used in Hacl.Impl.P256.Qinv
val lemma_l_ferm: unit ->
  Lemma (let r = modp_inv2_prime (pow2 256) order in (pow r (order - 1) % order == 1))

let lemma_l_ferm () =
  let r = modp_inv2_prime (pow2 256) order in
  assert_norm (exp (modp_inv2_prime (pow2 256) order) (order - 1) == 1);
  Hacl.Spec.P256.Lemmas.lemma_pow_mod_n_is_fpow order r (order - 1)


val lemma_multiplication_not_mod_prime_left: a:nat{a < prime} -> Lemma
  (requires a * (modp_inv2 (pow2 256)) % prime == 0)
  (ensures a == 0)

let lemma_multiplication_not_mod_prime_left a =
  let b = modp_inv2 (pow2 256) in
  Math.Lemmas.lemma_mod_mul_distr_r a b prime;
  assert (a * b % prime == a * (b % prime) % prime);
  let r = -26959946654596436328278158470660195847911760999080590586820792680449 in
  let s = 26959946660873538059280334323183841250350249843923952699046031785985 in
  assert_norm (r * prime + s * b == 1);
  Math.Lemmas.swap_mul a b;
  assert (b * a % prime == 0);
  Math.Euclid.euclid prime b a r s;
  assert (a % prime == 0);
  Math.Lemmas.small_mod a prime


// used in Hacl.Impl.P256.PointAdd, Hacl.Impl.P256.PointMul, Hacl.Impl.P256.Point
val lemma_multiplication_not_mod_prime: a:nat{a < prime} ->
  Lemma (a * (modp_inv2 (pow2 256)) % prime == 0 <==> a == 0)

let lemma_multiplication_not_mod_prime a =
  Classical.move_requires lemma_multiplication_not_mod_prime_left a
