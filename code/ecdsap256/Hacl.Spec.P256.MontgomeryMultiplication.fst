module Hacl.Spec.P256.MontgomeryMultiplication

open FStar.Mul

module S = Spec.P256

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let fmont_R = pow2 256
let fmont_R_inv = S.modp_inv2_prime (pow2 256) S.prime

let from_mont (a:int) : S.felem = a * fmont_R_inv % S.prime
let to_mont   (a:int) : S.felem = a * fmont_R % S.prime

let from_mont_point (a:tuple3 nat nat nat) : S.jacob_point =
  let x, y, z = a in from_mont x, from_mont y, from_mont z


val lemmaToDomainAndBackIsTheSame: a:S.felem -> Lemma (from_mont (to_mont a) == a)
let lemmaToDomainAndBackIsTheSame a =
  calc (==) {
    from_mont (to_mont a); // == a
    (==) { }
    (a * fmont_R % S.prime) * fmont_R_inv % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a * fmont_R) fmont_R_inv S.prime }
    a * fmont_R * fmont_R_inv % S.prime;
    (==) { Math.Lemmas.paren_mul_right a fmont_R fmont_R_inv }
    a * (fmont_R * fmont_R_inv) % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r a (fmont_R * fmont_R_inv) S.prime }
    a * (fmont_R * fmont_R_inv % S.prime) % S.prime;
    (==) { assert_norm (fmont_R * fmont_R_inv % S.prime = 1) }
    a % S.prime;
    (==) { Math.Lemmas.modulo_lemma a S.prime }
    a;
  }


val lemmaFromDomainToDomain: a:S.felem -> Lemma (to_mont (from_mont a) == a)
let lemmaFromDomainToDomain a =
  calc (==) {
    to_mont (from_mont a); // == a
    (==) { }
    (a * fmont_R_inv % S.prime) * fmont_R % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a * fmont_R_inv) fmont_R S.prime }
    a * fmont_R_inv * fmont_R % S.prime;
    (==) { Math.Lemmas.paren_mul_right a fmont_R_inv fmont_R }
    a * (fmont_R_inv * fmont_R) % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r a (fmont_R_inv * fmont_R) S.prime }
    a * (fmont_R_inv * fmont_R % S.prime) % S.prime;
    (==) { assert_norm (fmont_R_inv * fmont_R % S.prime = 1) }
    a % S.prime;
    (==) { Math.Lemmas.modulo_lemma a S.prime }
    a;
  }


val inDomain_mod_is_not_mod: a:int -> Lemma (to_mont a == to_mont (a % S.prime))
let inDomain_mod_is_not_mod a =
  calc (==) {
    to_mont (a % S.prime);
    (==) { }
    (a % S.prime) * fmont_R % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l a fmont_R S.prime }
    a * fmont_R % S.prime;
  }


val fmont_mul_lemma: a:S.felem -> b:S.felem ->
  Lemma (S.fmul (from_mont a) (from_mont b) = from_mont ((a * b * fmont_R_inv) % S.prime))

let fmont_mul_lemma a b =
  calc (==) {
    (from_mont a * from_mont b) % S.prime;
    (==) { }
    ((a * fmont_R_inv % S.prime) * (b * fmont_R_inv % S.prime)) % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l
      (a * fmont_R_inv) (b * fmont_R_inv % S.prime) S.prime }
    (a * fmont_R_inv * (b * fmont_R_inv % S.prime)) % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (a * fmont_R_inv) (b * fmont_R_inv) S.prime }
    (a * fmont_R_inv * (b * fmont_R_inv)) % S.prime;
    (==) { Math.Lemmas.paren_mul_right a fmont_R_inv (b * fmont_R_inv) }
    (a * (fmont_R_inv * (b * fmont_R_inv))) % S.prime;
    (==) { Math.Lemmas.paren_mul_right fmont_R_inv b fmont_R_inv }
    (a * (fmont_R_inv * b * fmont_R_inv)) % S.prime;
    (==) { Math.Lemmas.swap_mul fmont_R_inv b }
    (a * (b * fmont_R_inv * fmont_R_inv)) % S.prime;
    (==) { Math.Lemmas.paren_mul_right a (b * fmont_R_inv) fmont_R_inv }
    (a * (b * fmont_R_inv) * fmont_R_inv) % S.prime;
    (==) { Math.Lemmas.paren_mul_right a b fmont_R_inv }
    (a * b * fmont_R_inv * fmont_R_inv) % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a * b * fmont_R_inv) fmont_R_inv S.prime }
    from_mont ((a * b * fmont_R_inv) % S.prime);
  }


val fmont_add_lemma: a:S.felem -> b:S.felem ->
  Lemma (S.fadd (from_mont a) (from_mont b) = from_mont ((a + b) % S.prime))

let fmont_add_lemma a b =
  calc (==) {
    (from_mont a + from_mont b) % S.prime;
    (==) { }
    (a * fmont_R_inv % S.prime + b * fmont_R_inv % S.prime) % S.prime;
    (==) { Math.Lemmas.modulo_distributivity (a * fmont_R_inv) (b * fmont_R_inv) S.prime }
    (a * fmont_R_inv + b * fmont_R_inv) % S.prime;
    (==) { Math.Lemmas.distributivity_add_left a b fmont_R_inv }
    (a + b) * fmont_R_inv % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a + b) fmont_R_inv S.prime }
    (a + b) % S.prime * fmont_R_inv % S.prime;
    (==) { }
    from_mont ((a + b) % S.prime);
  }


val fmont_sub_lemma: a:S.felem -> b:S.felem ->
  Lemma (S.fsub (from_mont a) (from_mont b) = from_mont ((a - b) % S.prime))

let fmont_sub_lemma a b =
  calc (==) {
    (from_mont a - from_mont b) % S.prime;
    (==) { }
    (a * fmont_R_inv % S.prime - b * fmont_R_inv % S.prime) % S.prime;
    (==) { Math.Lemmas.lemma_mod_sub_distr (a * fmont_R_inv % S.prime) (b * fmont_R_inv) S.prime }
    (a * fmont_R_inv % S.prime - b * fmont_R_inv) % S.prime;
    (==) { Math.Lemmas.lemma_mod_plus_distr_l (a * fmont_R_inv) (- b * fmont_R_inv) S.prime }
    (a * fmont_R_inv - b * fmont_R_inv) % S.prime;
    (==) { Math.Lemmas.distributivity_sub_left a b fmont_R_inv }
    (a - b) * fmont_R_inv % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a - b) fmont_R_inv S.prime }
    (a - b) % S.prime * fmont_R_inv % S.prime;
    (==) { }
    from_mont ((a - b) % S.prime);
  }
