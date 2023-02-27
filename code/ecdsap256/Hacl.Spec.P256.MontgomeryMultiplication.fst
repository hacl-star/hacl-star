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
let lemmaFromDomain a = ()

val lemmaToDomain: a:int -> Lemma (toDomain_ a == a * mont_R % S.prime)
let lemmaToDomain a = ()

val lemmaToDomainAndBackIsTheSame: a:S.felem -> Lemma (fromDomain_ (toDomain_ a) == a)
  [SMTPat (fromDomain_ (toDomain_ a))]
let lemmaToDomainAndBackIsTheSame a =
  calc (==) {
    fromDomain_ (toDomain_ a); // == a
    (==) { }
    (a * mont_R % S.prime) * mont_R_inv % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a * mont_R) mont_R_inv S.prime }
    a * mont_R * mont_R_inv % S.prime;
    (==) { Math.Lemmas.paren_mul_right a mont_R mont_R_inv }
    a * (mont_R * mont_R_inv) % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r a (mont_R * mont_R_inv) S.prime }
    a * (mont_R * mont_R_inv % S.prime) % S.prime;
    (==) { assert_norm (mont_R * mont_R_inv % S.prime = 1) }
    a % S.prime;
    (==) { Math.Lemmas.modulo_lemma a S.prime }
    a;
  }


val lemmaFromDomainToDomain: a:S.felem -> Lemma (toDomain_ (fromDomain_ a) == a)
let lemmaFromDomainToDomain a =
  calc (==) {
    toDomain_ (fromDomain_ a); // == a
    (==) { }
    (a * mont_R_inv % S.prime) * mont_R % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a * mont_R_inv) mont_R S.prime }
    a * mont_R_inv * mont_R % S.prime;
    (==) { Math.Lemmas.paren_mul_right a mont_R_inv mont_R }
    a * (mont_R_inv * mont_R) % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r a (mont_R_inv * mont_R) S.prime }
    a * (mont_R_inv * mont_R % S.prime) % S.prime;
    (==) { assert_norm (mont_R_inv * mont_R % S.prime = 1) }
    a % S.prime;
    (==) { Math.Lemmas.modulo_lemma a S.prime }
    a;
  }


val inDomain_mod_is_not_mod: a:int -> Lemma (toDomain_ a == toDomain_ (a % S.prime))
let inDomain_mod_is_not_mod a =
  calc (==) {
    toDomain_ (a % S.prime); // == toDomain_ a
    (==) { }
    (a % S.prime) * mont_R % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l a mont_R S.prime }
    a * mont_R % S.prime;
  }


val multiplicationInDomainNat: #k:S.felem -> #l:S.felem
  -> a:S.felem{a == toDomain_ k}
  -> b:S.felem{b == toDomain_ l} ->
  Lemma (a * b * mont_R_inv % S.prime == toDomain_ (k * l))

let multiplicationInDomainNat #k #l a b =
  // a = k * mont_R % S.prime = toDomain_ k
  // b = l * mont_R % S.prime = toDomain_ l
  calc (==) {
    a * b * mont_R_inv % S.prime; // == toDomain_ (k * l)
    (==) { }
    a * (l * mont_R % S.prime) * mont_R_inv % S.prime;
    (==) { Math.Lemmas.paren_mul_right a (l * mont_R % S.prime) mont_R_inv }
    a * ((l * mont_R % S.prime) * mont_R_inv) % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r a ((l * mont_R % S.prime) * mont_R_inv) S.prime }
    a * ((l * mont_R % S.prime) * mont_R_inv % S.prime) % S.prime;
    (==) { lemmaToDomainAndBackIsTheSame l }
    (k * mont_R % S.prime) * l % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (k * mont_R) l S.prime }
    (k * mont_R) * l % S.prime;
    (==) { Math.Lemmas.paren_mul_right k mont_R l;
      Math.Lemmas.swap_mul mont_R l;
      Math.Lemmas.paren_mul_right k l mont_R }
    (k * l) * mont_R % S.prime;
    (==) { }
    toDomain_ (k * l);
  }


val additionInDomain: a:S.felem -> b:S.felem ->
  Lemma ((a + b) % S.prime == toDomain_ (fromDomain_ a + fromDomain_ b))

let additionInDomain a b =
  let k = fromDomain_ a in
  let l = fromDomain_ b in
  calc (==) {
    (a + b) % S.prime;
    (==) { lemmaFromDomainToDomain a; lemmaFromDomainToDomain b }
    (toDomain_ k + toDomain_ l) % S.prime;
    (==) { }
    (k * mont_R % S.prime + l * mont_R % S.prime) % S.prime;
    (==) { Math.Lemmas.modulo_distributivity (k * mont_R) (l * mont_R) S.prime }
    (k * mont_R + l * mont_R) % S.prime;
    (==) { Math.Lemmas.distributivity_add_left k l mont_R }
    ((k + l) * mont_R) % S.prime;
    (==) { }
    toDomain_ (fromDomain_ a + fromDomain_ b);
  }


val substractionInDomain: a:S.felem -> b:S.felem ->
  Lemma ((a - b) % S.prime == toDomain_ (fromDomain_ a - fromDomain_ b))

let substractionInDomain a b =
  let k = fromDomain_ a in
  let l = fromDomain_ b in
  calc (==) {
    (a - b) % S.prime;
    (==) { lemmaFromDomainToDomain a; lemmaFromDomainToDomain b }
    (toDomain_ k - toDomain_ l) % S.prime;
    (==) { }
    (k * mont_R % S.prime - l * mont_R % S.prime) % S.prime;
    (==) { Math.Lemmas.lemma_mod_sub_distr (k * mont_R % S.prime) (l * mont_R) S.prime }
    (k * mont_R % S.prime - l * mont_R) % S.prime;
    (==) { Math.Lemmas.lemma_mod_add_distr (-(l * mont_R)) (k * mont_R) S.prime }
    (k * mont_R - l * mont_R) % S.prime;
    (==) { Math.Lemmas.distributivity_sub_left k l mont_R }
    ((k - l) * mont_R) % S.prime;
    (==) { }
    toDomain_ (fromDomain_ a - fromDomain_ b);
  }
