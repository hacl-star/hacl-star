module Hacl.Spec.P256.Montgomery

open FStar.Mul
open Lib.IntTypes

module S = Spec.P256
module M = Lib.NatMod

module BD = Hacl.Spec.Bignum.Definitions
module SBM = Hacl.Spec.Bignum.Montgomery
module SBML = Hacl.Spec.Montgomery.Lemmas

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///  Montgomery arithmetic for a base field

val lemma_abc_is_acb (a b c:nat) : Lemma (a * b * c = a * c * b)
let lemma_abc_is_acb a b c =
  Math.Lemmas.paren_mul_right a b c;
  Math.Lemmas.swap_mul b c;
  Math.Lemmas.paren_mul_right a c b


val lemma_mod_mul_assoc (n:pos) (a b c:nat) : Lemma ((a * b % n) * c % n == (a * (b * c % n)) % n)
let lemma_mod_mul_assoc m a b c =
  calc (==) {
    (a * b % m) * c % m;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a * b) c m }
    (a * b) * c % m;
    (==) { Math.Lemmas.paren_mul_right a b c }
    a * (b * c) % m;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r a (b * c) m }
    a * (b * c % m) % m;
  }


val lemma_to_from_mont_id_gen (n mont_R mont_R_inv:pos) (a:nat{a < n}) : Lemma
  (requires mont_R * mont_R_inv % n = 1)
  (ensures  (a * mont_R % n) * mont_R_inv % n == a)

let lemma_to_from_mont_id_gen n mont_R mont_R_inv a =
  lemma_mod_mul_assoc n a mont_R mont_R_inv;
  Math.Lemmas.modulo_lemma a n


val lemma_from_to_mont_id_gen (n mont_R mont_R_inv:pos) (a:nat{a < n}) : Lemma
  (requires mont_R_inv * mont_R % n = 1)
  (ensures  (a * mont_R_inv % n) * mont_R % n == a)

let lemma_from_to_mont_id_gen n mont_R mont_R_inv a =
  lemma_to_from_mont_id_gen n mont_R_inv mont_R a


val mont_mul_lemma_gen (n:pos) (mont_R_inv a b: nat) :
  Lemma (((a * mont_R_inv % n) * (b * mont_R_inv % n)) % n ==
    ((a * b * mont_R_inv) % n) * mont_R_inv % n)

let mont_mul_lemma_gen n mont_R_inv a b =
  calc (==) {
    ((a * mont_R_inv % n) * (b * mont_R_inv % n)) % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l
      (a * mont_R_inv) (b * mont_R_inv % n) n }
    (a * mont_R_inv * (b * mont_R_inv % n)) % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (a * mont_R_inv) (b * mont_R_inv) n }
    (a * mont_R_inv * (b * mont_R_inv)) % n;
    (==) { Math.Lemmas.paren_mul_right a mont_R_inv (b * mont_R_inv) }
    (a * (mont_R_inv * (b * mont_R_inv))) % n;
    (==) { Math.Lemmas.paren_mul_right mont_R_inv b mont_R_inv }
    (a * (mont_R_inv * b * mont_R_inv)) % n;
    (==) { Math.Lemmas.swap_mul mont_R_inv b }
    (a * (b * mont_R_inv * mont_R_inv)) % n;
    (==) { Math.Lemmas.paren_mul_right a (b * mont_R_inv) mont_R_inv }
    (a * (b * mont_R_inv) * mont_R_inv) % n;
    (==) { Math.Lemmas.paren_mul_right a b mont_R_inv }
    (a * b * mont_R_inv * mont_R_inv) % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a * b * mont_R_inv) mont_R_inv n }
    ((a * b * mont_R_inv) % n) * mont_R_inv % n;
  }


val mont_add_lemma_gen (n:pos) (mont_R_inv a b: nat) :
  Lemma ((a * mont_R_inv % n + b * mont_R_inv % n) % n == (a + b) % n * mont_R_inv % n)

let mont_add_lemma_gen n mont_R_inv a b =
  calc (==) {
    (a * mont_R_inv % n + b * mont_R_inv % n) % n;
    (==) { Math.Lemmas.modulo_distributivity (a * mont_R_inv) (b * mont_R_inv) n }
    (a * mont_R_inv + b * mont_R_inv) % n;
    (==) { Math.Lemmas.distributivity_add_left a b mont_R_inv }
    (a + b) * mont_R_inv % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a + b) mont_R_inv n }
    (a + b) % n * mont_R_inv % n;
  }


val mont_sub_lemma_gen (n:pos) (mont_R_inv a b: nat) :
  Lemma ((a * mont_R_inv % n - b * mont_R_inv % n) % n == (a - b) % n * mont_R_inv % n)

let mont_sub_lemma_gen n mont_R_inv a b =
  calc (==) {
    (a * mont_R_inv % n - b * mont_R_inv % n) % n;
    (==) { Math.Lemmas.lemma_mod_sub_distr (a * mont_R_inv % n) (b * mont_R_inv) n }
    (a * mont_R_inv % n - b * mont_R_inv) % n;
    (==) { Math.Lemmas.lemma_mod_plus_distr_l (a * mont_R_inv) (- b * mont_R_inv) n }
    (a * mont_R_inv - b * mont_R_inv) % n;
    (==) { Math.Lemmas.distributivity_sub_left a b mont_R_inv }
    (a - b) * mont_R_inv % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a - b) mont_R_inv n }
    (a - b) % n * mont_R_inv % n;
  }


val lemma_mont_inv_gen (n:pos{1 < n}) (mont_R:pos) (mont_R_inv:nat{mont_R_inv < n}) (a:nat{a < n}) :
  Lemma
  (requires M.pow_mod #n mont_R_inv (n - 2) == mont_R % n)
  (ensures  M.pow_mod #n (a * mont_R_inv % n) (n - 2) == M.pow_mod #n a (n - 2) * mont_R % n)

let lemma_mont_inv_gen n mont_R mont_R_inv k =
  M.lemma_pow_mod #n (k * mont_R_inv % n) (n - 2);
  // assert (M.pow_mod #n (k * mont_R_inv % n) (n - 2) ==
    // M.pow (k * mont_R_inv % n) (n - 2) % n);

  M.lemma_pow_mod_base (k * mont_R_inv) (n - 2) n;
  // == M.pow (k * mont_R_inv) (n - 2) % n
  M.lemma_pow_mul_base k mont_R_inv (n - 2);
  // == M.pow k (n - 2) * M.pow mont_R_inv (n - 2) % n
  Math.Lemmas.lemma_mod_mul_distr_r (M.pow k (n - 2)) (M.pow mont_R_inv (n - 2)) n;
  // == M.pow k (n - 2) * (M.pow mont_R_inv (n - 2) % n) % n
  M.lemma_pow_mod #n mont_R_inv (n - 2);
  assert (M.pow_mod #n (k * mont_R_inv % n) (n - 2) == M.pow k (n - 2) * (mont_R % n) % n);

  Math.Lemmas.lemma_mod_mul_distr_r (M.pow k (n - 2)) mont_R n;
  // == M.pow k (n - 2) * mont_R % n
  Math.Lemmas.lemma_mod_mul_distr_l (M.pow k (n - 2)) mont_R n;
  // == M.pow k (n - 2) % n * mont_R % n
  M.lemma_pow_mod #n k (n - 2)


let mont_cancel_lemma_gen n mont_R mont_R_inv a b =
  calc (==) {
    (a * mont_R % n * b * mont_R_inv) % n;
    (==) { Math.Lemmas.paren_mul_right (a * mont_R % n) b mont_R_inv }
    (a * mont_R % n * (b * mont_R_inv)) % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a * mont_R) (b * mont_R_inv) n }
    (a * mont_R * (b * mont_R_inv)) % n;
    (==) { Math.Lemmas.paren_mul_right a mont_R (b * mont_R_inv);
           Math.Lemmas.swap_mul mont_R (b * mont_R_inv) }
    (a * (b * mont_R_inv * mont_R)) % n;
    (==) { Math.Lemmas.paren_mul_right b mont_R_inv mont_R }
    (a * (b * (mont_R_inv * mont_R))) % n;
    (==) { Math.Lemmas.paren_mul_right a b (mont_R_inv * mont_R) }
    (a * b * (mont_R_inv * mont_R)) % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (a * b) (mont_R_inv * mont_R) n }
    (a * b * (mont_R_inv * mont_R % n)) % n;
    (==) { assert (mont_R_inv * mont_R % n = 1) }
    (a * b) % n;
  }


let fmont_R_inv =
  let d, _ = SBML.eea_pow2_odd 256 S.prime in d % S.prime


let mul_fmont_R_and_R_inv_is_one () =
  let d, k = SBML.eea_pow2_odd 256 S.prime in
  SBML.mont_preconditions_d 64 4 S.prime;
  assert (d * pow2 256 % S.prime = 1);
  Math.Lemmas.lemma_mod_mul_distr_l d (pow2 256) S.prime

//--------------------------------------//
// bn_mont_reduction is x * fmont_R_inv //
//--------------------------------------//

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
    BD.bn_v x * d % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (BD.bn_v x) d S.prime }
    BD.bn_v x * (d % S.prime) % S.prime;
    (==) { }
    BD.bn_v x * fmont_R_inv % S.prime;
  }

//---------------------------

let lemma_from_mont_zero a =
  Spec.P256.Lemmas.prime_lemma ();
  Lib.NatMod.lemma_mul_mod_prime_zero #S.prime a fmont_R_inv


let lemma_to_from_mont_id a =
  mul_fmont_R_and_R_inv_is_one ();
  lemma_to_from_mont_id_gen S.prime fmont_R fmont_R_inv a


let lemma_from_to_mont_id a =
  mul_fmont_R_and_R_inv_is_one ();
  lemma_from_to_mont_id_gen S.prime fmont_R fmont_R_inv a


let fmont_mul_lemma a b =
  mont_mul_lemma_gen S.prime fmont_R_inv a b


let fmont_add_lemma a b =
  mont_add_lemma_gen S.prime fmont_R_inv a b


let fmont_sub_lemma a b =
  mont_sub_lemma_gen S.prime fmont_R_inv a b


///  Montgomery arithmetic for a scalar field

let qmont_R_inv =
  let d, _ = SBML.eea_pow2_odd 256 S.order in d % S.order


let mul_qmont_R_and_R_inv_is_one () =
  let d, k = SBML.eea_pow2_odd 256 S.order in
  SBML.mont_preconditions_d 64 4 S.order;
  assert (d * pow2 256 % S.order = 1);
  Math.Lemmas.lemma_mod_mul_distr_l d (pow2 256) S.order;
  assert (d % S.order * pow2 256 % S.order = 1)

//--------------------------------------//
// bn_mont_reduction is x * qmont_R_inv //
//--------------------------------------//

val lemma_order_mont: unit ->
  Lemma (S.order % 2 = 1 /\ S.order < pow2 256 /\ (1 + S.order * 0xccd1c8aaee00bc4f) % pow2 64 = 0)

let lemma_order_mont () =
  assert_norm (S.order % 2 = 1);
  assert_norm (S.order < pow2 256);
  assert_norm ((1 + S.order * 0xccd1c8aaee00bc4f) % pow2 64 = 0)


let bn_qmont_reduction_lemma x n =
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
    (==) { }
    (BD.bn_v x) * qmont_R_inv % S.order;
  }

//--------------------------

let lemma_to_from_qmont_id a =
  mul_qmont_R_and_R_inv_is_one ();
  lemma_to_from_mont_id_gen S.order qmont_R qmont_R_inv a


let lemma_from_to_qmont_id a =
  mul_qmont_R_and_R_inv_is_one ();
  Math.Lemmas.swap_mul qmont_R qmont_R_inv;
  lemma_from_to_mont_id_gen S.order qmont_R qmont_R_inv a


let qmont_add_lemma a b =
  mont_add_lemma_gen S.order qmont_R_inv a b


let qmont_mul_lemma a b =
  mont_mul_lemma_gen S.order qmont_R_inv a b


let qmont_inv_lemma k =
  assert_norm (M.pow_mod_ #S.order qmont_R_inv (S.order - 2) == qmont_R % S.order);
  M.pow_mod_def #S.order qmont_R_inv (S.order - 2);
  assert (M.pow_mod #S.order qmont_R_inv (S.order - 2) == qmont_R % S.order);

  lemma_mont_inv_gen S.order qmont_R qmont_R_inv k;
  assert (M.pow_mod #S.order (k * qmont_R_inv % S.order) (S.order - 2) ==
    M.pow_mod #S.order k (S.order - 2) * qmont_R % S.order);
  assert (S.qinv (k * qmont_R_inv % S.order) == S.qinv k * qmont_R % S.order)


val qmont_cancel_lemma1: a:S.qelem -> b:S.qelem ->
  Lemma ((a * qmont_R % S.order * b * qmont_R_inv) % S.order = a * b % S.order)

let qmont_cancel_lemma1 a b =
  mul_qmont_R_and_R_inv_is_one ();
  mont_cancel_lemma_gen S.order qmont_R qmont_R_inv a b


val qmont_cancel_lemma2: a:S.qelem -> b:S.qelem ->
  Lemma (to_qmont a * from_qmont b % S.order = a * b % S.order)

let qmont_cancel_lemma2 a b =
  calc (==) {
    to_qmont a * from_qmont b % S.order;
    (==) { }
    (a * qmont_R % S.order * (b * qmont_R_inv % S.order)) % S.order;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (a * qmont_R % S.order) (b * qmont_R_inv) S.order }
    (a * qmont_R % S.order * (b * qmont_R_inv)) % S.order;
    (==) { Math.Lemmas.paren_mul_right (a * qmont_R % S.order) b qmont_R_inv }
    (a * qmont_R % S.order * b * qmont_R_inv) % S.order;
    (==) { qmont_cancel_lemma1 a b }
    a * b % S.order;
  }


let qmont_inv_mul_lemma s sinv b =
  let s_mont = from_qmont s in
  let b_mont = from_qmont b in
  calc (==) {
    (sinv * b_mont * qmont_R_inv) % S.order;
    (==) { lemma_from_to_qmont_id sinv }
    (S.qinv s_mont * qmont_R % S.order * b_mont * qmont_R_inv) % S.order;
    (==) { qmont_cancel_lemma1 (S.qinv s_mont) b_mont }
    S.qinv s_mont * b_mont % S.order;
    (==) { qmont_inv_lemma s }
    (S.qinv s * qmont_R % S.order * (b * qmont_R_inv % S.order)) % S.order;
    (==) { qmont_cancel_lemma2 (S.qinv s) b }
    S.qinv s * b % S.order;
  }


let lemma_ecdsa_sign_s k kinv r d_a m =
  let s = (from_qmont m + from_qmont (r * d_a)) % S.order in
  calc (==) { // s =
    (m * qmont_R_inv % S.order + (r * d_a * qmont_R_inv) % S.order) % S.order;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (r * d_a) qmont_R_inv S.order }
    (m * qmont_R_inv % S.order + (S.qmul r d_a * qmont_R_inv) % S.order) % S.order;
    (==) { qmont_add_lemma m (S.qmul r d_a) }
    (S.qadd m (S.qmul r d_a)) * qmont_R_inv % S.order;
    (==) { }
    from_qmont (S.qadd m (S.qmul r d_a));
    };

  calc (==) {
    (kinv * s * qmont_R_inv) % S.order;
    (==) { lemma_abc_is_acb kinv s qmont_R_inv }
    (kinv * qmont_R_inv * s) % S.order;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (kinv * qmont_R_inv) s S.order }
    ((kinv * qmont_R_inv % S.order) * s) % S.order;
    (==) { }
    to_qmont (S.qinv k) * s % S.order;
    (==) { qmont_cancel_lemma2 (S.qinv k) (S.qadd m (S.qmul r d_a)) }
    (S.qinv k * (S.qadd m (S.qmul r d_a))) % S.order;
  }
