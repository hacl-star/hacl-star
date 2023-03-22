module Hacl.Spec.P256.Montgomery

open FStar.Mul

module S = Spec.P256

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///  Montgomery arithmetic for a base field

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


let lemma_multiplication_not_mod_prime a =
  Classical.move_requires lemma_multiplication_not_mod_prime_left a


let lemma_to_from_mont_id a =
  calc (==) {
    from_mont (to_mont a); // == a
    (==) { }
    (a * fmont_R % S.prime) * fmont_R_inv % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a * fmont_R) fmont_R_inv S.prime }
    a * fmont_R * fmont_R_inv % S.prime;
    (==) { Math.Lemmas.paren_mul_right a fmont_R fmont_R_inv }
    a * (fmont_R * fmont_R_inv) % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r a (fmont_R * fmont_R_inv) S.prime }
    a * (fmont_R * fmont_R_inv % S.prime) % S.prime;
    (==) { assert_norm (fmont_R * fmont_R_inv % S.prime = 1) }
    a % S.prime;
    (==) { Math.Lemmas.modulo_lemma a S.prime }
    a;
  }


let lemma_from_to_mont_id a =
  calc (==) {
    to_mont (from_mont a); // == a
    (==) { }
    (a * fmont_R_inv % S.prime) * fmont_R % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a * fmont_R_inv) fmont_R S.prime }
    a * fmont_R_inv * fmont_R % S.prime;
    (==) { Math.Lemmas.paren_mul_right a fmont_R_inv fmont_R }
    a * (fmont_R_inv * fmont_R) % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r a (fmont_R_inv * fmont_R) S.prime }
    a * (fmont_R_inv * fmont_R % S.prime) % S.prime;
    (==) { assert_norm (fmont_R_inv * fmont_R % S.prime = 1) }
    a % S.prime;
    (==) { Math.Lemmas.modulo_lemma a S.prime }
    a;
  }


let fmont_mul_lemma a b =
  calc (==) {
    (from_mont a * from_mont b) % S.prime;
    (==) { }
    ((a * fmont_R_inv % S.prime) * (b * fmont_R_inv % S.prime)) % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l
      (a * fmont_R_inv) (b * fmont_R_inv % S.prime) S.prime }
    (a * fmont_R_inv * (b * fmont_R_inv % S.prime)) % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (a * fmont_R_inv) (b * fmont_R_inv) S.prime }
    (a * fmont_R_inv * (b * fmont_R_inv)) % S.prime;
    (==) { Math.Lemmas.paren_mul_right a fmont_R_inv (b * fmont_R_inv) }
    (a * (fmont_R_inv * (b * fmont_R_inv))) % S.prime;
    (==) { Math.Lemmas.paren_mul_right fmont_R_inv b fmont_R_inv }
    (a * (fmont_R_inv * b * fmont_R_inv)) % S.prime;
    (==) { Math.Lemmas.swap_mul fmont_R_inv b }
    (a * (b * fmont_R_inv * fmont_R_inv)) % S.prime;
    (==) { Math.Lemmas.paren_mul_right a (b * fmont_R_inv) fmont_R_inv }
    (a * (b * fmont_R_inv) * fmont_R_inv) % S.prime;
    (==) { Math.Lemmas.paren_mul_right a b fmont_R_inv }
    (a * b * fmont_R_inv * fmont_R_inv) % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a * b * fmont_R_inv) fmont_R_inv S.prime }
    from_mont ((a * b * fmont_R_inv) % S.prime);
  }


let fmont_add_lemma a b =
  calc (==) {
    (from_mont a + from_mont b) % S.prime;
    (==) { }
    (a * fmont_R_inv % S.prime + b * fmont_R_inv % S.prime) % S.prime;
    (==) { Math.Lemmas.modulo_distributivity (a * fmont_R_inv) (b * fmont_R_inv) S.prime }
    (a * fmont_R_inv + b * fmont_R_inv) % S.prime;
    (==) { Math.Lemmas.distributivity_add_left a b fmont_R_inv }
    (a + b) * fmont_R_inv % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a + b) fmont_R_inv S.prime }
    (a + b) % S.prime * fmont_R_inv % S.prime;
    (==) { }
    from_mont ((a + b) % S.prime);
  }


let fmont_sub_lemma a b =
  calc (==) {
    (from_mont a - from_mont b) % S.prime;
    (==) { }
    (a * fmont_R_inv % S.prime - b * fmont_R_inv % S.prime) % S.prime;
    (==) { Math.Lemmas.lemma_mod_sub_distr (a * fmont_R_inv % S.prime) (b * fmont_R_inv) S.prime }
    (a * fmont_R_inv % S.prime - b * fmont_R_inv) % S.prime;
    (==) { Math.Lemmas.lemma_mod_plus_distr_l (a * fmont_R_inv) (- b * fmont_R_inv) S.prime }
    (a * fmont_R_inv - b * fmont_R_inv) % S.prime;
    (==) { Math.Lemmas.distributivity_sub_left a b fmont_R_inv }
    (a - b) * fmont_R_inv % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a - b) fmont_R_inv S.prime }
    (a - b) % S.prime * fmont_R_inv % S.prime;
    (==) { }
    from_mont ((a - b) % S.prime);
  }


///  Montgomery arithmetic for a scalar field

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
