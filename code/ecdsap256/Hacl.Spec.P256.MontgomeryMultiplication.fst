module Hacl.Spec.P256.MontgomeryMultiplication

open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Mul

open Lib.IntTypes
open Lib.ByteSequence

open Spec.P256
open Hacl.Spec.P256.Lemmas

#set-options "--z3rlimit 40 --fuel 0 --ifuel 0"

let fromDomain_ a = (a * modp_inv2 (pow2 256)) % prime


let fromDomainPoint a =
  let x, y, z = a in
  fromDomain_ x, fromDomain_ y, fromDomain_ z


let toDomain_ a = (a * pow2 256) % prime


let lemmaFromDomain a = ()


let lemmaToDomain a = ()


let lemmaToDomainAndBackIsTheSame a =
  let to = toDomain_ a in
  lemmaToDomain a;
  let from = fromDomain_ to in
  lemmaFromDomain to;
  lemma_mod_mul_distr_l (a * pow2 256) (modp_inv2 (pow2 256)) prime;
  assert_norm (pow2 256 * modp_inv2 (pow2 256) % prime = 1);
  modulo_distributivity_mult_last_two a 1 1 (pow2 256) (modp_inv2 (pow2 256)) prime;
  modulo_lemma a prime


let lemmaFromDomainToDomain a =
  let from = fromDomain_ a in
  lemmaFromDomain a;
  let to = toDomain_ from in
  lemmaToDomain from;
  lemma_mod_mul_distr_l (a * modp_inv2 (pow2 256)) (pow2 256)  prime;
  assert_norm (modp_inv2 (pow2 256) * (pow2 256) % prime = 1);
  modulo_distributivity_mult_last_two a 1 1 (modp_inv2 (pow2 256)) (pow2 256) prime;
  modulo_lemma a prime


let inDomain_mod_is_not_mod a =
  lemma_mod_mul_distr_l a (pow2 256) prime


let multiplicationInDomainNat #k #l a b =
  assert_norm (prime > 3);
  let multResult = a * b * modp_inv2_prime (pow2 256) prime % prime in
  modulo_distributivity_mult2 (k * pow2 256) (l * pow2 256) (modp_inv2_prime (pow2 256) prime) prime;
  lemma_twice_brackets k (pow2 256) 1 l (pow2 256) 1 (modp_inv2 (pow2 256));
  assert_norm (pow2 256 * modp_inv2 (pow2 256) % prime == 1);
  modulo_distributivity_mult_last_two k (pow2 256) l (pow2 256) (modp_inv2 (pow2 256)) prime;
  lemma_mul_associativity_3 k (pow2 256) l

let additionInDomain a b =
  let k = fromDomain_ a in
  let l = fromDomain_ b in
  calc (==) {
    (a + b) % prime;
    == { lemmaFromDomainToDomain a; lemmaFromDomainToDomain b }
    (toDomain_ k + toDomain_ l) % prime;
    == { }
    (k * pow2 256 % prime + l * pow2 256 % prime) % prime;
    == { modulo_distributivity (k * pow2 256) (l * pow2 256) prime }
    (k * pow2 256 + l * pow2 256) % prime;
    == { distributivity_add_left k l (pow2 256) }
    ((k + l) * pow2 256) % prime;
    == { }
    toDomain_ (fromDomain_ a + fromDomain_ b);
  }


let substractionInDomain a b =
  let k = fromDomain_ a in
  let l = fromDomain_ b in
  calc (==) {
    (a - b) % prime;
    == { lemmaFromDomainToDomain a; lemmaFromDomainToDomain b }
    (toDomain_ k - toDomain_ l) % prime;
    == { }
    (k * pow2 256 % prime - l * pow2 256 % prime) % prime;
    == { lemma_mod_sub_distr (k * pow2 256 % prime) (l * pow2 256) prime }
    (k * pow2 256 % prime - l * pow2 256) % prime;
    == { lemma_mod_add_distr (-(l * pow2 256)) (k * pow2 256) prime }
    (k * pow2 256 - l * pow2 256) % prime;
    == { distributivity_sub_left k l (pow2 256) }
    ((k - l) * pow2 256) % prime;
    == { }
    toDomain_ (fromDomain_ a - fromDomain_ b);
  }
