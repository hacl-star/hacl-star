module Hacl.Spec.MontgomeryMultiplication

open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Mul

open Spec.ECC
open Spec.ECC.Curves
open Hacl.Lemmas.P256
open Hacl.Spec.EC.Definition

open Lib.IntTypes
open Lib.Sequence

#set-options "--z3rlimit 40 --fuel 0 --ifuel 0"

noextract
val fromDomain_: #c: curve -> a: int -> Tot (a: nat {a < getPrime c})

noextract
val fromDomainPoint: #c: curve -> a: point_nat_prime #c -> 
  Tot (r: point_nat_prime #c {
    let x, y, z = a in
    let x3, y3, z3 = r in 
    x3 == fromDomain_ #c x /\ y3 == fromDomain_ #c y /\ z3 == fromDomain_ #c z}
  )

noextract
val toDomain_: #c: curve -> a: int -> Tot nat

val lemmaFromDomain: #c: curve -> a: int -> Lemma (fromDomain_ #c a == a * modp_inv2 #c (pow2 (getPower c)) % getPrime c)

val lemmaToDomain: #c: curve -> a: int -> Lemma (toDomain_ #c a == a * (pow2 (getPower c)) % getPrime c)

val lemmaToDomainAndBackIsTheSame: #c: curve -> a: nat {a < getPrime c} ->
  Lemma (fromDomain_ #c (toDomain_ #c a) == a)
  [SMTPat (fromDomain_ #c (toDomain_ #c a))]

val lemmaFromDomainToDomain: #c: curve -> a: nat {a < getPrime c} -> 
  Lemma (toDomain_ #c (fromDomain_ #c a) == a)

val lemmaFromDomainToDomainModuloPrime: #c: curve -> a: int -> 
  Lemma (a % (getPrime c) == fromDomain_ #c (toDomain_ #c a))

val inDomain_mod_is_not_mod: #c: curve -> a: int ->
  Lemma (toDomain_ #c a == toDomain_ #c (a % getPrime c))

val multiplicationInDomainNat: #c: curve -> 
  #k: nat -> #l: nat ->
  a: nat {a == toDomain_ #c k /\ a < getPrime c} -> 
  b: nat {b == toDomain_ #c l /\ b < getPrime c} ->
  Lemma (
    let prime = getPrime c in 
    let multResult = a * b * modp_inv2_prime (pow2 (getPower c)) prime % prime in 
    multResult == toDomain_ #c (k * l))

val additionInDomain: #c: curve -> a: nat {a < getPrime c} -> b: nat {b < getPrime c} -> Lemma 
  ((a + b) % getPrime c == toDomain_ #c (fromDomain_ #c a + fromDomain_ #c b))
  
val substractionInDomain: #c: curve ->  a: nat {a < getPrime c} -> b: nat {b < getPrime c} -> Lemma 
  ((a - b) % getPrime c == toDomain_ #c (fromDomain_ #c a - fromDomain_ #c b))


val _pow_step0: #c: curve -> p:nat_prime #c -> q:nat_prime #c -> tuple2 (nat_prime #c) (nat_prime #c)

val _pow_step1: #c: curve -> p:nat_prime #c -> q:nat_prime #c -> tuple2 (nat_prime #c) (nat_prime #c)

let swap (#c: curve) (p:nat_prime #c) (q:nat_prime #c) = q, p

val conditional_swap_pow: #c: curve -> i:uint64 -> p:nat_prime #c -> q:nat_prime #c -> tuple2 (nat_prime #c) (nat_prime #c)

val lemma_swaped_steps: #c: curve ->  p: nat_prime -> q: nat_prime ->
  Lemma (
    let afterSwapP, afterSwapQ = swap p q in
    let p1, q1 = _pow_step0 afterSwapP afterSwapQ in
    let p2, q2 = swap p1 q1 in
    let r0, r1 = _pow_step1 #c p q in
    p2 == r0 /\ q2 == r1)

val _pow_step: #c: curve -> k: scalar_bytes #c -> i:nat{i < getPower c} 
  -> before: tuple2 (nat_prime #c) (nat_prime #c)
  -> tuple2 (nat_prime #c) (nat_prime #c)

val pow_spec: #c: curve -> k:scalar_bytes #c
  -> a:nat_prime #c
  -> Tot (r: nat_prime #c {r = pow a (Lib.ByteSequence.nat_from_bytes_le k) % getPrime c})

val sq_root_spec: #c: curve -> a: nat_prime #c 
  -> Tot (r: nat_prime #c {let prime = getPrime c in  r = pow a ((prime + 1) / 4) % prime})
