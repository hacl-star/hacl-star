module Hacl.Spec.P256.MontgomeryMultiplication

open FStar.Mul

module S = Spec.P256

#set-options "--z3rlimit 40 --fuel 0 --ifuel 0"

let lemmaFromDomain a = ()

let lemmaToDomain a = ()

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


let inDomain_mod_is_not_mod a =
  calc (==) {
    toDomain_ (a % S.prime); // == toDomain_ a
    (==) { }
    (a % S.prime) * mont_R % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l a mont_R S.prime }
    a * mont_R % S.prime;
  }


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
