module Hacl.Spec.P256.Montgomery

open FStar.Mul
open Lib.IntTypes

module S = Spec.P256
module M = Lib.NatMod
module LSeq = Lib.Sequence

module BD = Hacl.Spec.Bignum.Definitions
module SBM = Hacl.Spec.Bignum.Montgomery
module SBML = Hacl.Spec.Montgomery.Lemmas

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


val lemma_abc_is_acb (a b c:nat) : Lemma (a * b * c = a * c * b)
let lemma_abc_is_acb a b c =
  Math.Lemmas.paren_mul_right a b c;
  Math.Lemmas.swap_mul b c;
  Math.Lemmas.paren_mul_right a c b


//--------------------------------------//
// bn_mont_reduction is x * fmont_R_inv //
//--------------------------------------//

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


val mont_R_inv_is_bn_mont_d: unit -> Lemma
  (requires S.prime % 2 = 1)
  (ensures  (let d, _ = SBML.eea_pow2_odd 256 S.prime in fmont_R_inv == d % S.prime))

let mont_R_inv_is_bn_mont_d () =
  let d, k = SBML.eea_pow2_odd 256 S.prime in
  SBML.mont_preconditions_d 64 4 S.prime;
  assert (d * pow2 256 % S.prime = 1);

  assert_norm (fmont_R * fmont_R_inv % S.prime = 1);
  Math.Lemmas.lemma_mod_mul_distr_l (pow2 256) fmont_R_inv S.prime;
  assert (fmont_R_inv * pow2 256 % S.prime = 1);

  assert (fmont_R_inv * pow2 256 % S.prime = d * pow2 256 % S.prime);
  lemma_mod_mul_pow256_prime fmont_R_inv d;
  assert (fmont_R_inv % S.prime == d % S.prime);
  Math.Lemmas.modulo_lemma fmont_R_inv S.prime;
  assert (fmont_R_inv == d % S.prime)


val lemma_prime_mont: unit ->
  Lemma (S.prime % 2 = 1 /\ S.prime < pow2 256 /\ (1 + S.prime) % pow2 64 = 0)

let lemma_prime_mont () =
  assert_norm (S.prime % 2 = 1);
  assert_norm (S.prime < pow2 256);
  assert_norm ((1 + S.prime) % pow2 64 = 0)


let bn_mont_reduction_lemma x n =
  lemma_prime_mont ();
  assert (SBM.bn_mont_pre n (u64 1));
  let d, _ = SBML.eea_pow2_odd 256 (BD.bn_v n) in

  let res = SBM.bn_mont_reduction n (u64 1) x in
  assert_norm (S.prime * S.prime < S.prime * pow2 256);
  assert (BD.bn_v x < S.prime * pow2 256);

  SBM.bn_mont_reduction_lemma n (u64 1) x;
  assert (BD.bn_v res == SBML.mont_reduction 64 4 (BD.bn_v n) 1 (BD.bn_v x));
  SBML.mont_reduction_lemma 64 4 (BD.bn_v n) 1 (BD.bn_v x);
  assert (BD.bn_v res == BD.bn_v x * d % S.prime);
  calc (==) {
    (BD.bn_v x) * d % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (BD.bn_v x) d S.prime }
    (BD.bn_v x) * (d % S.prime) % S.prime;
    (==) { mont_R_inv_is_bn_mont_d () }
    (BD.bn_v x) * fmont_R_inv % S.prime;
  }

//---------------------------

val lemma_multiplication_not_mod_prime_left: a:S.felem -> Lemma
  (requires a * fmont_R_inv % S.prime == 0)
  (ensures a == 0)

let lemma_multiplication_not_mod_prime_left a =
  let b = fmont_R_inv in
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

//--------------------------------------//
// bn_mont_reduction is x * qmont_R_inv //
//--------------------------------------//

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


val qmont_R_inv_is_bn_mont_d: unit -> Lemma
  (requires S.order % 2 = 1)
  (ensures  (let d, _ = SBML.eea_pow2_odd 256 S.order in qmont_R_inv == d % S.order))

let qmont_R_inv_is_bn_mont_d () =
  let d, k = SBML.eea_pow2_odd 256 S.order in
  SBML.mont_preconditions_d 64 4 S.order;
  assert (d * pow2 256 % S.order = 1);

  assert_norm (qmont_R * qmont_R_inv % S.order = 1);
  Math.Lemmas.lemma_mod_mul_distr_l (pow2 256) qmont_R_inv S.order;
  assert (qmont_R_inv * pow2 256 % S.order = 1);

  assert (qmont_R_inv * pow2 256 % S.order = d * pow2 256 % S.order);
  lemma_mod_mul_pow256_order qmont_R_inv d;
  assert (qmont_R_inv % S.order == d % S.order);
  Math.Lemmas.modulo_lemma qmont_R_inv S.order;
  assert (qmont_R_inv == d % S.order)


val lemma_order_mont: unit ->
  Lemma (S.order % 2 = 1 /\ S.order < pow2 256 /\ (1 + S.order * 0xccd1c8aaee00bc4f) % pow2 64 = 0)

let lemma_order_mont () =
  assert_norm (S.order % 2 = 1);
  assert_norm (S.order < pow2 256);
  assert_norm ((1 + S.order * 0xccd1c8aaee00bc4f) % pow2 64 = 0)


let qmont_reduction_lemma x n =
  let k0 = 0xccd1c8aaee00bc4f in
  lemma_order_mont ();
  assert (SBM.bn_mont_pre n (u64 k0));
  let d, _ = SBML.eea_pow2_odd 256 (BD.bn_v n) in

  let res = SBM.bn_mont_reduction n (u64 k0) x in
  assert_norm (S.order * S.order < S.order * pow2 256);
  assert (BD.bn_v x < S.order * pow2 256);

  SBM.bn_mont_reduction_lemma n (u64 k0) x;
  assert (BD.bn_v res == SBML.mont_reduction 64 4 (BD.bn_v n) k0 (BD.bn_v x));
  SBML.mont_reduction_lemma 64 4 (BD.bn_v n) k0 (BD.bn_v x);
  assert (BD.bn_v res == BD.bn_v x * d % S.order);
  calc (==) {
    (BD.bn_v x) * d % S.order;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (BD.bn_v x) d S.order }
    (BD.bn_v x) * (d % S.order) % S.order;
    (==) { qmont_R_inv_is_bn_mont_d () }
    (BD.bn_v x) * qmont_R_inv % S.order;
  }

//--------------------------

// toDomain_ (fromDomain_ a) == a
let lemmaFromDomainToDomain a =
  calc (==) {
    toDomain_ (fromDomain_ a); // == a
    (==) { }
    (a * qmont_R_inv % S.order) * qmont_R % S.order;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a * qmont_R_inv) qmont_R S.order }
    a * qmont_R_inv * qmont_R % S.order;
    (==) { Math.Lemmas.paren_mul_right a qmont_R_inv qmont_R }
    a * (qmont_R_inv * qmont_R) % S.order;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r a (qmont_R_inv * qmont_R) S.order }
    a * (qmont_R_inv * qmont_R % S.order) % S.order;
    (==) { assert_norm (qmont_R_inv * qmont_R % S.order = 1) }
    a % S.order;
    (==) { Math.Lemmas.modulo_lemma a S.order }
    a;
  }


// fromDomain_ (toDomain_ a) == a
let lemmaToDomainFromDomain a =
  calc (==) {
    fromDomain_ (toDomain_ a); // == a
    (==) { }
    (a * qmont_R % S.order) * qmont_R_inv % S.order;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a * qmont_R) qmont_R_inv S.order }
    a * qmont_R * qmont_R_inv % S.order;
    (==) { Math.Lemmas.paren_mul_right a qmont_R qmont_R_inv }
    a * (qmont_R * qmont_R_inv) % S.order;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r a (qmont_R * qmont_R_inv) S.order }
    a * (qmont_R * qmont_R_inv % S.order) % S.order;
    (==) { assert_norm (qmont_R * qmont_R_inv % S.order = 1) }
    a % S.order;
    (==) { Math.Lemmas.modulo_lemma a S.order }
    a;
  }


let qadd_lemma a b =
  calc (==) {
    (fromDomain_ a + fromDomain_ b) % S.order;
    (==) { }
    (a * qmont_R_inv % S.order + b * qmont_R_inv % S.order) % S.order;
    (==) { Math.Lemmas.modulo_distributivity (a * qmont_R_inv) (b * qmont_R_inv) S.order }
    (a * qmont_R_inv + b * qmont_R_inv) % S.order;
    (==) { Math.Lemmas.distributivity_add_left a b qmont_R_inv }
    (a + b) * qmont_R_inv % S.order;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a + b) qmont_R_inv S.order }
    (a + b) % S.order * qmont_R_inv % S.order;
    (==) { }
    fromDomain_ ((a + b) % S.order);
  }


let qmul_lemma a b =
  calc (==) {
    (fromDomain_ a * fromDomain_ b) % S.order;
    (==) { }
    ((a * qmont_R_inv % S.order) * (b * qmont_R_inv % S.order)) % S.order;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l
      (a * qmont_R_inv) (b * qmont_R_inv % S.order) S.order }
    (a * qmont_R_inv * (b * qmont_R_inv % S.order)) % S.order;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (a * qmont_R_inv) (b * qmont_R_inv) S.order }
    (a * qmont_R_inv * (b * qmont_R_inv)) % S.order;
    (==) { Math.Lemmas.paren_mul_right a qmont_R_inv (b * qmont_R_inv) }
    (a * (qmont_R_inv * (b * qmont_R_inv))) % S.order;
    (==) { Math.Lemmas.paren_mul_right qmont_R_inv b qmont_R_inv }
    (a * (qmont_R_inv * b * qmont_R_inv)) % S.order;
    (==) { Math.Lemmas.swap_mul qmont_R_inv b }
    (a * (b * qmont_R_inv * qmont_R_inv)) % S.order;
    (==) { Math.Lemmas.paren_mul_right a (b * qmont_R_inv) qmont_R_inv }
    (a * (b * qmont_R_inv) * qmont_R_inv) % S.order;
    (==) { Math.Lemmas.paren_mul_right a b qmont_R_inv }
    (a * b * qmont_R_inv * qmont_R_inv) % S.order;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a * b * qmont_R_inv) qmont_R_inv S.order }
    fromDomain_ ((a * b * qmont_R_inv) % S.order);
  }


let lemma_mont_qinv k =
  assert_norm (M.pow_mod_ #S.order qmont_R_inv (S.order - 2) == qmont_R % S.order);
  M.pow_mod_def #S.order qmont_R_inv (S.order - 2);
  assert (M.pow_mod #S.order qmont_R_inv (S.order - 2) == qmont_R % S.order);

  M.lemma_pow_mod #S.order (k * qmont_R_inv % S.order) (S.order - 2);
  //assert (S.qinv (fromDomain_ k) ==
    //(M.pow (k * qmont_R_inv % S.order) (S.order - 2)) % S.order);

  M.lemma_pow_mod_base (k * qmont_R_inv) (S.order - 2) S.order;
  // assert (S.qinv (fromDomain_ k) == (M.pow (k * qmont_R_inv) (S.order - 2)) % S.order);
  M.lemma_pow_mul_base k qmont_R_inv (S.order - 2);
  // assert (S.qinv (fromDomain_ k) ==
    // (M.pow k (S.order - 2) * M.pow qmont_R_inv (S.order - 2)) % S.order);
  Math.Lemmas.lemma_mod_mul_distr_r
    (M.pow k (S.order - 2)) (M.pow qmont_R_inv (S.order - 2)) S.order;
  // assert (S.qinv (fromDomain_ k) ==
    // (M.pow k (S.order - 2) * M.pow qmont_R_inv (S.order - 2) % S.order) % S.order);
  M.lemma_pow_mod #S.order qmont_R_inv (S.order - 2);
  assert (S.qinv (fromDomain_ k) ==
    (M.pow k (S.order - 2) * (qmont_R % S.order)) % S.order);
  Math.Lemmas.lemma_mod_mul_distr_r (M.pow k (S.order - 2)) qmont_R S.order;
  //assert (S.qinv (fromDomain_ k) == (M.pow k (S.order - 2) * qmont_R) % S.order);
  Math.Lemmas.lemma_mod_mul_distr_l (M.pow k (S.order - 2)) qmont_R S.order;
  //assert (S.qinv (fromDomain_ k) == (M.pow k (S.order - 2) % S.order * qmont_R) % S.order);
  M.lemma_pow_mod #S.order k (S.order - 2)


let lemma_cancel_mont a b =
  calc (==) {
    (a * qmont_R % S.order * b * qmont_R_inv) % S.order;
    (==) { Math.Lemmas.paren_mul_right (a * qmont_R % S.order) b qmont_R_inv }
    (a * qmont_R % S.order * (b * qmont_R_inv)) % S.order;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a * qmont_R) (b * qmont_R_inv) S.order }
    (a * qmont_R * (b * qmont_R_inv)) % S.order;
    (==) { Math.Lemmas.paren_mul_right a qmont_R (b * qmont_R_inv);
           Math.Lemmas.swap_mul qmont_R (b * qmont_R_inv) }
    (a * (b * qmont_R_inv * qmont_R)) % S.order;
    (==) { Math.Lemmas.paren_mul_right b qmont_R_inv qmont_R }
    (a * (b * (qmont_R_inv * qmont_R))) % S.order;
    (==) { Math.Lemmas.paren_mul_right a b (qmont_R_inv * qmont_R) }
    (a * b * (qmont_R_inv * qmont_R)) % S.order;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (a * b) (qmont_R_inv * qmont_R) S.order }
    (a * b * (qmont_R_inv * qmont_R % S.order)) % S.order;
    (==) { assert_norm (qmont_R_inv * qmont_R % S.order = 1) }
    (a * b) % S.order;
  }


let qmul_mont_lemma s sinv b =
  let s_mont = fromDomain_ s in
  let b_mont = fromDomain_ b in
  calc (==) {
    (sinv * b_mont * qmont_R_inv) % S.order;
    (==) { lemmaFromDomainToDomain sinv }
    (S.qinv s_mont * qmont_R % S.order * b_mont * qmont_R_inv) % S.order;
    (==) { lemma_cancel_mont (S.qinv s_mont) b_mont }
    (S.qinv s_mont * b_mont) % S.order;
    (==) { lemma_mont_qinv s }
    ((S.qinv s * qmont_R % S.order) * (b * qmont_R_inv % S.order)) % S.order;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r
      (S.qinv s * qmont_R % S.order) (b * qmont_R_inv) S.order }
    ((S.qinv s * qmont_R % S.order) * (b * qmont_R_inv)) % S.order;
    (==) { Math.Lemmas.paren_mul_right (S.qinv s * qmont_R % S.order) b qmont_R_inv }
    ((S.qinv s * qmont_R % S.order) * b * qmont_R_inv) % S.order;
    (==) { lemma_cancel_mont (S.qinv s) b }
    S.qinv s * b % S.order;
  }


let lemma_ecdsa_sign_s k kinv r d_a m =
  let s = (m * qmont_R_inv % S.order + (r * d_a * qmont_R_inv) % S.order) % S.order in
  calc (==) { // s =
    (m * qmont_R_inv % S.order + (r * d_a * qmont_R_inv) % S.order) % S.order;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (r * d_a) qmont_R_inv S.order }
    (m * qmont_R_inv % S.order + (S.qmul r d_a * qmont_R_inv) % S.order) % S.order;
    (==) { Math.Lemmas.modulo_distributivity (m * qmont_R_inv)
      (S.qmul r d_a * qmont_R_inv) S.order }
    (m * qmont_R_inv + S.qmul r d_a * qmont_R_inv) % S.order;
    (==) { Math.Lemmas.distributivity_add_left m (S.qmul r d_a) qmont_R_inv }
    (m + S.qmul r d_a) * qmont_R_inv % S.order;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (m + S.qmul r d_a) qmont_R_inv S.order }
    (S.qadd m (S.qmul r d_a)) * qmont_R_inv % S.order;
    };

  calc (==) {
    (kinv * s * qmont_R_inv) % S.order;
    (==) { lemma_abc_is_acb kinv s qmont_R_inv }
    (kinv * qmont_R_inv * s) % S.order;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (kinv * qmont_R_inv) s S.order }
    ((kinv * qmont_R_inv % S.order) * s) % S.order;
    (==) { }
    ((S.qinv k * qmont_R % S.order) * s) % S.order;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (S.qinv k * qmont_R) s S.order }
    (S.qinv k * qmont_R * s) % S.order;
    (==) { }
    (S.qinv k * qmont_R * ((S.qadd m (S.qmul r d_a)) * qmont_R_inv % S.order)) % S.order;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (S.qinv k * qmont_R)
      ((S.qadd m (S.qmul r d_a)) * qmont_R_inv) S.order }
    (S.qinv k * qmont_R * ((S.qadd m (S.qmul r d_a)) * qmont_R_inv)) % S.order;
    (==) { lemma_abc_is_acb (S.qinv k) qmont_R ((S.qadd m (S.qmul r d_a)) * qmont_R_inv) }
    (S.qinv k * ((S.qadd m (S.qmul r d_a)) * qmont_R_inv) * qmont_R) % S.order;
    (==) { Math.Lemmas.paren_mul_right (S.qinv k) (S.qadd m (S.qmul r d_a)) qmont_R_inv }
    (S.qinv k * (S.qadd m (S.qmul r d_a)) * qmont_R_inv * qmont_R) % S.order;
    (==) { Math.Lemmas.paren_mul_right (S.qinv k * (S.qadd m (S.qmul r d_a)))
      qmont_R_inv qmont_R }
    (S.qinv k * (S.qadd m (S.qmul r d_a)) * (qmont_R_inv * qmont_R)) % S.order;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (S.qinv k * (S.qadd m (S.qmul r d_a)))
      (qmont_R_inv * qmont_R) S.order }
    (S.qinv k * (S.qadd m (S.qmul r d_a)) * (qmont_R_inv * qmont_R % S.order)) % S.order;
    (==) { assert_norm (qmont_R_inv * qmont_R % S.order = 1) }
    (S.qinv k * (S.qadd m (S.qmul r d_a))) % S.order;
    }
