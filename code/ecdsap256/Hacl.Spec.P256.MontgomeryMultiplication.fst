module Hacl.Spec.P256.MontgomeryMultiplication

open FStar.Mul

module S = Spec.P256

#set-options "--z3rlimit 40 --fuel 0 --ifuel 0"

let mont_R = pow2 256
let mont_R_inv = S.modp_inv2_prime (pow2 256) S.prime

let fromDomain_ (a:int) : S.felem = a * mont_R_inv % S.prime
let toDomain_   (a:int) : S.felem = a * mont_R % S.prime

let fromDomainPoint (a:tuple3 nat nat nat) : S.jacob_point =
  let x, y, z = a in
  fromDomain_ x, fromDomain_ y, fromDomain_ z


// TODO: rm if we expose the defs of fromDomain and toDomain
val lemmaFromDomain: a:int -> Lemma (fromDomain_ a == a * mont_R_inv % S.prime)
let lemmaFromDomain a = ()

val lemmaToDomain: a:int -> Lemma (toDomain_ a == a * mont_R % S.prime)
let lemmaToDomain a = ()

val lemmaToDomainAndBackIsTheSame: a:S.felem -> Lemma (fromDomain_ (toDomain_ a) == a)
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


val fmont_mul_lemma: a:S.felem -> b:S.felem ->
  Lemma (S.fmul (fromDomain_ a) (fromDomain_ b) = fromDomain_ ((a * b * mont_R_inv) % S.prime))

let fmont_mul_lemma a b =
  calc (==) {
    (fromDomain_ a * fromDomain_ b) % S.prime;
    (==) { }
    ((a * mont_R_inv % S.prime) * (b * mont_R_inv % S.prime)) % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l
      (a * mont_R_inv) (b * mont_R_inv % S.prime) S.prime }
    (a * mont_R_inv * (b * mont_R_inv % S.prime)) % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (a * mont_R_inv) (b * mont_R_inv) S.prime }
    (a * mont_R_inv * (b * mont_R_inv)) % S.prime;
    (==) { Math.Lemmas.paren_mul_right a mont_R_inv (b * mont_R_inv) }
    (a * (mont_R_inv * (b * mont_R_inv))) % S.prime;
    (==) { Math.Lemmas.paren_mul_right mont_R_inv b mont_R_inv }
    (a * (mont_R_inv * b * mont_R_inv)) % S.prime;
    (==) { Math.Lemmas.swap_mul mont_R_inv b }
    (a * (b * mont_R_inv * mont_R_inv)) % S.prime;
    (==) { Math.Lemmas.paren_mul_right a (b * mont_R_inv) mont_R_inv }
    (a * (b * mont_R_inv) * mont_R_inv) % S.prime;
    (==) { Math.Lemmas.paren_mul_right a b mont_R_inv }
    (a * b * mont_R_inv * mont_R_inv) % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a * b * mont_R_inv) mont_R_inv S.prime }
    fromDomain_ ((a * b * mont_R_inv) % S.prime);
  }


val fmont_add_lemma: a:S.felem -> b:S.felem ->
  Lemma (S.fadd (fromDomain_ a) (fromDomain_ b) = fromDomain_ ((a + b) % S.prime))

let fmont_add_lemma a b =
  calc (==) {
    (fromDomain_ a + fromDomain_ b) % S.prime;
    (==) { }
    (a * mont_R_inv % S.prime + b * mont_R_inv % S.prime) % S.prime;
    (==) { Math.Lemmas.modulo_distributivity (a * mont_R_inv) (b * mont_R_inv) S.prime }
    (a * mont_R_inv + b * mont_R_inv) % S.prime;
    (==) { Math.Lemmas.distributivity_add_left a b mont_R_inv }
    (a + b) * mont_R_inv % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a + b) mont_R_inv S.prime }
    (a + b) % S.prime * mont_R_inv % S.prime;
    (==) { }
    fromDomain_ ((a + b) % S.prime);
  }


val fmont_sub_lemma: a:S.felem -> b:S.felem ->
  Lemma (S.fsub (fromDomain_ a) (fromDomain_ b) = fromDomain_ ((a - b) % S.prime))

let fmont_sub_lemma a b =
  calc (==) {
    (fromDomain_ a - fromDomain_ b) % S.prime;
    (==) { }
    (a * mont_R_inv % S.prime - b * mont_R_inv % S.prime) % S.prime;
    (==) { Math.Lemmas.lemma_mod_sub_distr (a * mont_R_inv % S.prime) (b * mont_R_inv) S.prime }
    (a * mont_R_inv % S.prime - b * mont_R_inv) % S.prime;
    (==) { Math.Lemmas.lemma_mod_plus_distr_l (a * mont_R_inv) (- b * mont_R_inv) S.prime }
    (a * mont_R_inv - b * mont_R_inv) % S.prime;
    (==) { Math.Lemmas.distributivity_sub_left a b mont_R_inv }
    (a - b) * mont_R_inv % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a - b) mont_R_inv S.prime }
    (a - b) % S.prime * mont_R_inv % S.prime;
    (==) { }
    fromDomain_ ((a - b) % S.prime);
  }
