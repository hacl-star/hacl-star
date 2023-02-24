module Hacl.Spec.P256.MontgomeryMultiplication

open FStar.Mul

module S = Spec.P256

#set-options "--z3rlimit 40 --fuel 0 --ifuel 0"

let mont_R = pow2 256
let mont_R_inv = S.modp_inv2 (pow2 256)

let fromDomain_ (a:int) : S.felem = a * mont_R_inv % S.prime
let toDomain_   (a:int) : S.felem = a * mont_R % S.prime

let fromDomainPoint (a:tuple3 nat nat nat) =
  let x, y, z = a in
  fromDomain_ x, fromDomain_ y, fromDomain_ z


// TODO: rm if we expose the defs of fromDomain and toDomain
val lemmaFromDomain: a:int -> Lemma (fromDomain_ a == a * mont_R_inv % S.prime)
val lemmaToDomain: a:int -> Lemma (toDomain_ a == a * mont_R % S.prime)


val lemmaToDomainAndBackIsTheSame: a:S.felem -> Lemma (fromDomain_ (toDomain_ a) == a)
  [SMTPat (fromDomain_ (toDomain_ a))]

val lemmaFromDomainToDomain: a:S.felem -> Lemma (toDomain_ (fromDomain_ a) == a)


val inDomain_mod_is_not_mod: a:int -> Lemma (toDomain_ a == toDomain_ (a % S.prime))


val multiplicationInDomainNat: #k:S.felem -> #l:S.felem
  -> a:S.felem{a == toDomain_ k}
  -> b:S.felem{b == toDomain_ l} ->
  Lemma (a * b * mont_R_inv % S.prime == toDomain_ (k * l))

val additionInDomain: a:S.felem -> b:S.felem ->
  Lemma ((a + b) % S.prime == toDomain_ (fromDomain_ a + fromDomain_ b))

val substractionInDomain: a:S.felem -> b:S.felem ->
  Lemma ((a - b) % S.prime == toDomain_ (fromDomain_ a - fromDomain_ b))
