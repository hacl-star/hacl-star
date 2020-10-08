module Spec.P256.MontgomeryMultiplication

open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Mul

open Spec.P256.Lemmas
open Spec.P256.Definitions

open Lib.IntTypes
open Lib.Sequence

#set-options "--z3rlimit 40 --fuel 0 --ifuel 0"

noextract
val fromDomain_: a: int -> Tot (a: nat {a < prime256})

noextract
val fromDomainPoint: a: tuple3 nat nat nat -> Tot (r: tuple3 nat nat nat 
  {
    let x, y, z = a in
    let x3, y3, z3 = r in 
    x3 == fromDomain_ x /\ y3 == fromDomain_ y /\ z3 == fromDomain_ z /\
    x3 < prime256 /\ y3 < prime256 /\ z3 < prime256
  }
)

noextract
val toDomain_: a: int -> Tot nat

val lemmaFromDomain: a: int -> Lemma (fromDomain_ (a) == a * modp_inv2 (pow2 256) % prime256)

val lemmaToDomain: a: int -> Lemma (toDomain_(a) == a * (pow2 256) % prime256)

val lemmaToDomainAndBackIsTheSame: a: nat {a < prime256} -> Lemma (fromDomain_ (toDomain_ a) == a)
  [SMTPat (fromDomain_ (toDomain_ a))]

val lemmaFromDomainToDomain: a: nat { a < prime256} -> Lemma (toDomain_ (fromDomain_ a) == a)

val lemmaFromDomainToDomainModuloPrime: a: int -> Lemma (a % prime256 == fromDomain_(toDomain_ a))

val inDomain_mod_is_not_mod: a: int -> Lemma (toDomain_ a == toDomain_ (a % prime256))

val multiplicationInDomainNat: #k: nat -> #l: nat ->
  a: nat {a == toDomain_ k /\ a < prime256} -> 
  b: nat {b == toDomain_ l /\ b < prime256} ->
  Lemma (
    assert_norm (prime256 > 3);
    let multResult = a * b * modp_inv2_prime (pow2 256) prime256 % prime256 in 
    multResult == toDomain_ (k * l))

val additionInDomain: a: nat {a < prime256} -> b: nat {b < prime256} -> Lemma 
  ((a + b) % prime256 == toDomain_ (fromDomain_ a + fromDomain_ b))
  
val substractionInDomain: a: nat {a < prime256} -> b: nat { b < prime256} -> Lemma 
  ((a - b) % prime256 == toDomain_ (fromDomain_ a - fromDomain_ b))


val _pow_step0: p:nat_prime -> q:nat_prime -> tuple2 nat_prime nat_prime

val _pow_step1: p:nat_prime -> q:nat_prime -> tuple2 nat_prime nat_prime

let swap (p:nat_prime) (q:nat_prime) = q, p

val conditional_swap_pow: i:uint64 -> p:nat_prime -> q:nat_prime -> tuple2 nat_prime nat_prime

val lemma_swaped_steps: p: nat_prime -> q: nat_prime ->
  Lemma (
    let afterSwapP, afterSwapQ = swap p q in
    let p1, q1 = _pow_step0 afterSwapP afterSwapQ in
    let p2, q2 = swap p1 q1 in
    let r0, r1 = _pow_step1 p q in
    p2 == r0 /\ q2 == r1)


val _pow_step: k:lseq uint8 32 -> i:nat{i < 256} -> before:tuple2 nat_prime nat_prime
  -> tuple2 nat_prime nat_prime

val pow_spec: k:lseq uint8 32 -> a:nat_prime -> Tot (r: nat_prime {r = pow a (Lib.ByteSequence.nat_from_bytes_le k) % prime256})

val sq_root_spec: a: nat_prime -> Tot (r: nat_prime {r = pow a ((prime256 + 1) / 4) % prime256})
