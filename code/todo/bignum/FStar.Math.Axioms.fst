module FStar.Math.Axioms

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

assume val lemma_mod_sub_distr_l_l: a:nat -> b:nat -> p:pos -> Lemma ((a - b) % p = ((a % p) - b) % p)
assume val lemma_mod_sub_distr_l_r: a:nat -> b:nat -> p:pos -> Lemma ((a - b) % p = (a - (b % p)) % p)
assume val lemma_int_mod_mul_distr_l: a:int -> b:int -> p:pos -> Lemma
  (FStar.Mul.((a * b) % p = ((a % p) * b) % p))
