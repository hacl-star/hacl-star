module Hacl.Spec.P256.MontgomeryMultiplication

open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Spec.P256

#set-options "--z3rlimit 40 --fuel 0 --ifuel 0"

// used in Spec.P256.Montgomerymultiplication.PointAdd
val fromDomain_: a: int -> Tot (a: nat {a < prime})


val fromDomainPoint: a: tuple3 nat nat nat -> Tot (r: tuple3 nat nat nat
  {
    let x, y, z = a in
    let x3, y3, z3 = r in
    x3 == fromDomain_ x /\ y3 == fromDomain_ y /\ z3 == fromDomain_ z /\
    x3 < prime /\ y3 < prime /\ z3 < prime
  }
)


// used in Spec.P256.Montgomerymultiplication.PointAdd
val toDomain_: a: int -> Tot nat

val lemmaFromDomain: a: int -> Lemma (fromDomain_ (a) == a * modp_inv2 (pow2 256) % prime)

val lemmaToDomain: a: int -> Lemma (toDomain_(a) == a * (pow2 256) % prime)

// used in Hacl.Impl.P256.Compression
val lemmaToDomainAndBackIsTheSame: a: nat {a < prime} -> Lemma (fromDomain_ (toDomain_ a) == a)
  [SMTPat (fromDomain_ (toDomain_ a))]

// used in Hacl.Impl.P256.Field
val lemmaFromDomainToDomain: a: nat { a < prime} -> Lemma (toDomain_ (fromDomain_ a) == a)

// used in Hacl.Impl.P256.Field
val inDomain_mod_is_not_mod: a: int -> Lemma (toDomain_ a == toDomain_ (a % prime))

// used in Hacl.Impl.P256.Field
val multiplicationInDomainNat: #k: nat -> #l: nat ->
  a: nat {a == toDomain_ k /\ a < prime} ->
  b: nat {b == toDomain_ l /\ b < prime} ->
  Lemma (
    assert_norm (prime > 3);
    let multResult = a * b * modp_inv2_prime (pow2 256) prime % prime in
    multResult == toDomain_ (k * l))


// used in Hacl.Impl.P256.Field
val additionInDomain: a: nat {a < prime} -> b: nat {b < prime} -> Lemma
  ((a + b) % prime == toDomain_ (fromDomain_ a + fromDomain_ b))

// used in Hacl.Impl.P256.Field
val substractionInDomain: a: nat {a < prime} -> b: nat { b < prime} -> Lemma
  ((a - b) % prime == toDomain_ (fromDomain_ a - fromDomain_ b))


let swap (p:felem) (q:felem) = q, p
