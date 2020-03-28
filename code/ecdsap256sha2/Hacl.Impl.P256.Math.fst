module Hacl.Impl.P256.Math

open FStar.Math.Lemmas
open FStar.Math
open FStar.Mul

open Spec.P256.Lemmas

#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"

noextract
let prime256: (p: pos {p > 3}) =
  assert_norm (pow2 256 - pow2 224 + pow2 192 + pow2 96 -1 > 3);
  pow2 256 - pow2 224 + pow2 192 + pow2 96 -1
// 115792089210356248762697446949407573530086143415290314195533631308867097853951

val mod_sub: n:pos -> a:int -> b:int -> Lemma
  (requires a % n = b % n)
  (ensures  (a - b) % n = 0)
let mod_sub n a b =
  mod_add_both a b (-b) n

val sub_mod: n:pos -> a:int -> b:int -> Lemma
  (requires (a - b) % n = 0)
  (ensures  a % n = b % n)
let sub_mod n a b =
  mod_add_both (a - b) 0 b n

val mod_same: n:pos -> Lemma (n % n = 0)
let mod_same n = ()

val euclid: n:pos -> a:int -> b:int -> r:int -> s:int -> Lemma
  (requires (a * b) % n = 0 /\ r * n + s * a = 1)
  (ensures  b % n = 0)

let euclid n a b r s =
  calc (==) {
    b % n;
    == { FStar.Math.Lemmas.distributivity_add_left (r * n) (s * a) b }
    (r * n * b + s * a * b) % n;
    == { FStar.Math.Lemmas.paren_mul_right s a b }    
    (r * n * b + s * (a * b)) % n;
    == { FStar.Math.Lemmas.modulo_distributivity (r * n * b) (s * (a * b)) n }
    ((r * n * b) % n + s * (a * b) % n) % n;
    == { FStar.Math.Lemmas.lemma_mod_mul_distr_r s (a * b) n }
    ((r * n * b) % n + s * ((a * b) % n) % n) % n;  
    == { assert (a * b % n = 0) }
    ((r * n * b) % n + s * 0 % n) % n;
    == { assert (s * 0 == 0) }
    ((r * n * b) % n + 0 % n) % n;
    == { FStar.Math.Lemmas.modulo_lemma 0 n }
    ((r * n * b) % n) % n;
    == { FStar.Math.Lemmas.lemma_mod_twice (r * n * b) n }
    (r * n * b) % n;
    == { FStar.Math.Lemmas.swap_mul r n; FStar.Math.Lemmas.paren_mul_right n r b }
    (n * (r * b)) % n;
    == { FStar.Math.Lemmas.lemma_mod_mul_distr_l n (r * b) n}
    n % n * (r * b) % n;
    == { mod_same n }
    (0 * (r * b)) % n;
    == { assert (0 * (r * b) == 0) }
    0 % n;
    == { FStar.Math.Lemmas.modulo_lemma 0 n }
    0;
  }


val lemma_modular_multiplication_p256_2_left:
  a:nat{a < prime256} -> b:nat{b < prime256} -> Lemma
  (requires a * pow2 256 % prime256 = b * pow2 256 % prime256)
  (ensures  a == b)

let lemma_modular_multiplication_p256_2_left a b =
  mod_sub prime256 (a * pow2 256) (b * pow2 256);
  assert (pow2 256 * (a - b) % prime256 = 0);
  let r = 26959946654596436323893653559348051827142583427821597254581997273087 in
  let s = -26959946648319334592891477706824406424704094582978235142356758167551 in
  assert_norm (r * prime256 + s * pow2 256 = 1);
  euclid prime256 (pow2 256) (a - b) r s;
  assert ((a - b) % prime256 = 0);
  sub_mod prime256 a b;
  assert (a % prime256 = b % prime256);
  FStar.Math.Lemmas.modulo_lemma a prime256;
  FStar.Math.Lemmas.modulo_lemma b prime256

val lemma_modular_multiplication_p256_2: a: nat{a < prime256} -> b: nat{b < prime256} ->
  Lemma
  (a * pow2 256 % prime256 = b * pow2 256 % prime256 <==> a == b)

let lemma_modular_multiplication_p256_2 a b =
  Classical.move_requires_2 lemma_modular_multiplication_p256_2_left a b

noextract
let prime_p256_order:pos =
  assert_norm (115792089210356248762697446949407573529996955224135760342422259061068512044369> 0);
  115792089210356248762697446949407573529996955224135760342422259061068512044369

val lemma_montgomery_mod_inverse_addition: a:nat -> Lemma (
  a * modp_inv2_prime (pow2 64) prime256 * modp_inv2_prime (pow2 64) prime256 % prime256 ==
  a * modp_inv2_prime (pow2 128) prime256 % prime256)

let lemma_montgomery_mod_inverse_addition a =
  calc (==) {
    a * modp_inv2_prime (pow2 64) prime256 * modp_inv2_prime (pow2 64) prime256 % prime256;
    == { FStar.Math.Lemmas.paren_mul_right a (modp_inv2_prime (pow2 64) prime256) (modp_inv2_prime (pow2 64) prime256)}
    a * (modp_inv2_prime (pow2 64) prime256 * modp_inv2_prime (pow2 64) prime256) % prime256;
    == { FStar.Math.Lemmas.lemma_mod_mul_distr_r a
    (modp_inv2_prime (pow2 64) prime256 * modp_inv2_prime (pow2 64) prime256) prime256 }
    a * (modp_inv2_prime (pow2 64) prime256 * modp_inv2_prime (pow2 64) prime256 % prime256) % prime256;
    == { assert_norm (modp_inv2_prime (pow2 64) prime256 * modp_inv2_prime (pow2 64) prime256 % prime256 ==
    modp_inv2_prime (pow2 128) prime256 % prime256) }
    a * (modp_inv2_prime (pow2 128) prime256 % prime256) % prime256;
    == { FStar.Math.Lemmas.lemma_mod_mul_distr_r a (modp_inv2_prime (pow2 128) prime256) prime256 }
    a * modp_inv2_prime (pow2 128) prime256 % prime256;
  }

val lemma_montgomery_mod_inverse_addition2: a:nat -> Lemma (
  a * modp_inv2_prime (pow2 128) prime256 * modp_inv2_prime (pow2 128) prime256 % prime256 ==
  a * modp_inv2_prime (pow2 256) prime256 % prime256)

let lemma_montgomery_mod_inverse_addition2 a =
  calc (==) {
    a * modp_inv2_prime (pow2 128) prime256 * modp_inv2_prime (pow2 128) prime256 % prime256;
    == { FStar.Math.Lemmas.paren_mul_right a (modp_inv2_prime (pow2 128) prime256) (modp_inv2_prime (pow2 128) prime256)}
    a * (modp_inv2_prime (pow2 128) prime256 * modp_inv2_prime (pow2 128) prime256) % prime256;
    == { FStar.Math.Lemmas.lemma_mod_mul_distr_r a
    (modp_inv2_prime (pow2 128) prime256 * modp_inv2_prime (pow2 128) prime256) prime256 }
    a * (modp_inv2_prime (pow2 128) prime256 * modp_inv2_prime (pow2 128) prime256 % prime256) % prime256;
    == { assert_norm (modp_inv2_prime (pow2 128) prime256 * modp_inv2_prime (pow2 128) prime256 % prime256 ==
    modp_inv2_prime (pow2 256) prime256 % prime256) }
    a * (modp_inv2_prime (pow2 256) prime256 % prime256) % prime256;
    == { FStar.Math.Lemmas.lemma_mod_mul_distr_r a (modp_inv2_prime (pow2 256) prime256) prime256 }
    a * modp_inv2_prime (pow2 256) prime256 % prime256;
  }

(* Fermat's Little Theorem
   applied to r = modp_inv2_prime (pow2 256) prime_p256_order

  Verified in Sage:
   prime256 = Zmod(Integer(115792089210356248762697446949407573530086143415290314195533631308867097853951))
   p = 41058363725152142129326129780047268409114441015993725554835256314039467401291
   C = EllipticCurve(prime256, [-3, p])
   prime_p256_order =/ C.cardinality()
   Z = Integers(prime_p256_order)
   r = Z(inverse_mod(2**256, prime_p256_order))
   r ^ (prime_p256_order - 1)
*)
val lemma_l_ferm: unit -> Lemma
  (let r = modp_inv2_prime (pow2 256) prime_p256_order in
  (pow r (prime_p256_order - 1) % prime_p256_order == 1))

let lemma_l_ferm () =
  let r = modp_inv2_prime (pow2 256) prime_p256_order in
  assert_norm (exp (modp_inv2_prime (pow2 256) prime_p256_order) (prime_p256_order - 1)  == 1);
  lemma_pow_mod_n_is_fpow prime_p256_order r (prime_p256_order - 1)
  

val lemma_multiplication_not_mod_prime_left: a:nat{a < prime256} -> Lemma
  (requires a * (modp_inv2 (pow2 256)) % prime256 == 0)
  (ensures a == 0)

let lemma_multiplication_not_mod_prime_left a =
  let b = modp_inv2 (pow2 256) in
  lemma_mod_mul_distr_r a b prime256;
  assert (a * b % prime256 == a * (b % prime256) % prime256);
  let r = -26959946654596436328278158470660195847911760999080590586820792680449 in
  let s = 26959946660873538059280334323183841250350249843923952699046031785985 in
  assert_norm (r * prime256 + s * b == 1);
  swap_mul a b;
  assert (b * a % prime256 == 0);
  euclid prime256 b a r s;
  assert (a % prime256 == 0);
  small_mod a prime256

val lemma_multiplication_not_mod_prime: a:nat{a < prime256} ->
  Lemma (a * (modp_inv2 (pow2 256)) % prime256 == 0 <==> a == 0)

let lemma_multiplication_not_mod_prime a =
  Classical.move_requires lemma_multiplication_not_mod_prime_left a


val lemma_modular_multiplication_p256: a:nat{a < prime256} -> b:nat{b < prime256} -> Lemma
  (requires a * modp_inv2 (pow2 256) % prime256 == b * modp_inv2 (pow2 256) % prime256)
  (ensures  a == b)

let lemma_modular_multiplication_p256 a b =
  let c = modp_inv2 (pow2 256) in
  mod_sub prime256 (a * c) (b * c);
  assert (c * (a - b) % prime256 = 0);
  let r = -26959946654596436328278158470660195847911760999080590586820792680449 in
  let s = 26959946660873538059280334323183841250350249843923952699046031785985 in
  assert_norm (r * prime256 + s * c = 1);
  euclid prime256 c (a - b) r s;
  assert ((a - b) % prime256 = 0);
  sub_mod prime256 a b;
  assert (a % prime256 == b % prime256);
  FStar.Math.Lemmas.modulo_lemma a prime256;
  FStar.Math.Lemmas.modulo_lemma b prime256
