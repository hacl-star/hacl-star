module Hacl.Spec.P256.Math

open FStar.Mul
module S = Spec.P256

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


// used in Hacl.Impl.P256.Field
val lemma_mod_mul_pow256_prime: a:int -> b:int -> Lemma
  (requires a * pow2 256 % S.prime = b * pow2 256 % S.prime)
  (ensures  a % S.prime == b % S.prime)

let lemma_mod_mul_pow256_prime a b =
  mod_sub S.prime (a * pow2 256) (b * pow2 256);
  assert (pow2 256 * (a - b) % S.prime = 0);
  let r = 26959946654596436323893653559348051827142583427821597254581997273087 in
  let s = -26959946648319334592891477706824406424704094582978235142356758167551 in
  assert_norm (r * S.prime + s * pow2 256 = 1);
  FStar.Math.Euclid.euclid S.prime (pow2 256) (a - b) r s;
  assert ((a - b) % S.prime = 0);
  sub_mod S.prime a b;
  assert (a % S.prime = b % S.prime)


// used in Hacl.Impl.P256.Scalar
val lemma_mod_mul_pow256_order: a:int -> b:int -> Lemma
  (requires a * pow2 256 % S.order = b * pow2 256 % S.order)
  (ensures  a % S.order == b % S.order)

let lemma_mod_mul_pow256_order a b =
  mod_sub S.order (a * pow2 256) (b * pow2 256);
  assert (pow2 256 * (a - b) % S.order = 0);
  let r = -43790243024438006127650828685417305984841428635278707415088219106730833919055 in
  let s = 43790243014242295660885426880012836369732278457577312309071968676491870960761 in
  assert_norm (r * S.order + s * pow2 256 = 1);
  FStar.Math.Euclid.euclid S.order (pow2 256) (a - b) r s;
  assert ((a - b) % S.order = 0);
  sub_mod S.order a b;
  assert (a % S.order = b % S.order)


val lemma_multiplication_not_mod_prime_left: a:S.felem -> Lemma
  (requires a * (S.modp_inv2_prime (pow2 256) S.prime) % S.prime == 0)
  (ensures a == 0)

let lemma_multiplication_not_mod_prime_left a =
  let b = S.modp_inv2_prime (pow2 256) S.prime in
  Math.Lemmas.lemma_mod_mul_distr_r a b S.prime;
  assert (a * b % S.prime == a * (b % S.prime) % S.prime);
  let r = -26959946654596436328278158470660195847911760999080590586820792680449 in
  let s = 26959946660873538059280334323183841250350249843923952699046031785985 in
  assert_norm (r * S.prime + s * b == 1);
  Math.Lemmas.swap_mul a b;
  assert (b * a % S.prime == 0);
  Math.Euclid.euclid S.prime b a r s;
  assert (a % S.prime == 0);
  Math.Lemmas.small_mod a S.prime


// used in Hacl.Impl.P256.Point
val lemma_multiplication_not_mod_prime: a:S.felem ->
  Lemma (a * (S.modp_inv2_prime (pow2 256) S.prime) % S.prime == 0 <==> a == 0)

let lemma_multiplication_not_mod_prime a =
  Classical.move_requires lemma_multiplication_not_mod_prime_left a
