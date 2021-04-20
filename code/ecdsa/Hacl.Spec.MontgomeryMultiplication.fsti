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


type mode = |DH |DSA

let invert_mode (m: mode): Lemma
  (requires True)
  (ensures (inversion mode))
  [SMTPat (mode) ] = allow_inversion (mode)

let getModePrime (m: mode) (c: curve) : nat = match m with |DH -> getPrime c |DSA -> getOrder #c

let point_prime_mm #c #m = p: point_nat {let (x, y, z) = p in x < getModePrime m c /\ y < getModePrime m c /\ 
  z < getModePrime m c}


noextract
val fromDomain_: #c: curve -> #m: mode -> a: int -> Tot (a: nat {a < getModePrime m c})

noextract
val fromDomainPoint: #c: curve -> #m: mode -> a: point_nat ->
  Tot (r: point_prime_mm #c #m {
    let x, y, z = a in
    let x3, y3, z3 = r in 
    x3 == fromDomain_ #c #m x /\ y3 == fromDomain_ #c #m y /\ z3 == fromDomain_ #c #m z})


noextract
val toDomain_: #c: curve -> #m: mode -> a: int -> Tot nat

val lemmaFromDomain: #c: curve -> #m: mode -> a: int -> Lemma (fromDomain_ #c #m a == a * modp_inv2_prime (pow2 (getPower c)) (getModePrime m c) % getModePrime m c)

val lemmaToDomain: #c: curve -> #m: mode -> a: int -> Lemma (toDomain_ #c #m a == a * (pow2 (getPower c)) % getModePrime m c)

val lemmaToDomainFromDomain: #c: curve -> #m: mode -> a: nat {a < getModePrime m c} ->
  Lemma (fromDomain_ #c #m (toDomain_ #c #m a) == a)
  [SMTPat (fromDomain_ #c #m (toDomain_ #c #m a))]

val lemmaFromDomainToDomain: #c: curve -> #m: mode -> a: nat {a < getModePrime m c} -> 
  Lemma (toDomain_ #c #m (fromDomain_ #c #m a) == a)

val lemmaFromDomainToDomainModuloPrime: #c: curve -> #m: mode -> a: int -> 
  Lemma (a % (getModePrime m c) == fromDomain_ #c #m (toDomain_ #c #m a))

val lemmaToDomainFromDomainModuloPrime: #c: curve -> #m: mode -> a: int -> 
  Lemma (a % (getModePrime m c) == toDomain_ #c #m (fromDomain_ #c #m a))  

val inDomain_mod_is_not_mod: #c: curve -> #m: mode -> a: int ->
  Lemma (toDomain_ #c #m a == toDomain_ #c #m (a % getModePrime m c))

val multiplicationInDomainNat: #c: curve ->
  #k: nat -> #l: nat ->
  #m: mode ->
  a: nat {a == toDomain_ #c #m k /\ a < getModePrime m c} -> 
  b: nat {b == toDomain_ #c #m l /\ b < getModePrime m c} ->
  Lemma (let prime = getModePrime m c in 
    let multResult = a * b * modp_inv2_prime (pow2 (getPower c)) prime % prime in 
    multResult == toDomain_ #c #m (k * l))

val additionInDomain: #c: curve -> #m: mode -> a: nat {a < getModePrime m c} -> b: nat {b < getModePrime m c} -> Lemma (
  let prime = getModePrime m c in 
  (a + b) % prime == toDomain_ #c #m (fromDomain_ #c #m a + fromDomain_ #c #m b))
  
val substractionInDomain: #c: curve -> #m: mode -> a: nat {a < getModePrime m c} -> b: nat {b < getModePrime m c} -> Lemma (
  let prime = getModePrime m c in 
  (a - b) % prime == toDomain_ #c #m (fromDomain_ #c #m a - fromDomain_ #c #m b))


val _pow_step0: #c: curve -> #m: mode -> p: nat -> q: nat -> 
  tuple2 (r0: nat {r0 < getModePrime m c}) (r1: nat {r1 < getModePrime m c})

val _pow_step1: #c: curve -> #m: mode -> p:nat -> q:nat -> tuple2 (r0: nat {r0 < getModePrime m c}) (r1: nat {r1 < getModePrime m c})

let swap p q = q, p

val conditional_swap_pow: #c: curve -> i:uint64 -> nat -> nat -> tuple2 nat nat

val lemma_swaped_steps: #c: curve -> #m: mode -> p: nat -> q: nat -> Lemma (
  let afterSwapP, afterSwapQ = swap p q in
  let p1, q1 = _pow_step0 #c #m afterSwapP afterSwapQ in
  let p2, q2 = swap p1 q1 in
  let r0, r1 = _pow_step1 #c #m p q in
  p2 == r0 /\ q2 == r1)

val _pow_step: #c: curve -> #m: mode -> k: scalar_bytes #c -> i:nat{i < v (getScalarLen c)} 
  -> before: tuple2 (r0: nat {r0 < getModePrime m c}) (r1: nat {r1 < getModePrime m c})
  -> tuple2 (r0: nat {r0 < getModePrime m c}) (r1: nat {r1 < getModePrime m c})

val pow_spec: #c: curve -> #m: mode -> k:scalar_bytes #c
  -> a: nat {a < getModePrime m c}
  -> Tot (r: nat {r = pow a (Lib.ByteSequence.nat_from_bytes_le k) % getModePrime m c /\ r < getModePrime m c})

val sq_root_spec: #c: curve -> #m: mode -> a: nat {a < getModePrime m c}
  -> Tot (r: nat {let prime = getModePrime m c in r = pow a ((prime + 1) / 4) % prime /\ r < getModePrime m c})
