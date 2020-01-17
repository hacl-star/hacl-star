module Hacl.Math

open FStar.Math.Lemmas
open FStar.Math
open FStar.Mul

open Hacl.Spec.P256.Lemmas

noextract
let prime256: (p: pos {p > 3}) =
  assert_norm (pow2 256 - pow2 224 + pow2 192 + pow2 96 -1 > 3);
  pow2 256 - pow2 224 + pow2 192 + pow2 96 -1

noextract
let prime_p256_order:pos =
  assert_norm (115792089210356248762697446949407573529996955224135760342422259061068512044369> 0);
  115792089210356248762697446949407573529996955224135760342422259061068512044369


assume val lemma_montgomery_mod_inverse_addition: a: nat -> 
  Lemma (
    (a * modp_inv2_prime(pow2 64) prime256  * modp_inv2_prime (pow2 64) prime256) % prime256 == (a * modp_inv2_prime(pow2 128) prime256) % prime256)

assume val lemma_montgomery_mod_inverse_addition2: a: nat -> 
  Lemma (
    (a * modp_inv2_prime (pow2 128) prime256  * modp_inv2_prime (pow2 128) prime256) % prime256 == (a * modp_inv2_prime(pow2 256) prime256) % prime256)



val lemma_modular_multiplication_p256_2: a: nat{a < prime256} -> b: nat{b < prime256} -> 
  Lemma 
  (a * pow2 256 % prime256 = b * pow2 256 % prime256  <==> a == b)


let lemma_modular_multiplication_p256_2 a b = admit()

(* fermat little theorem *)
val lemma_l_ferm: a: nat -> Lemma (pow a (prime_p256_order - 1) % prime_p256_order == 1)

let lemma_l_ferm a = admit()
