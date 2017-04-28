module FStar.Math.Axioms

assume val lemma_mod_sub_distr_l_l: a:nat -> b:nat -> p:pos -> Lemma ((a - b) % p = ((a % p) - b) % p)
assume val lemma_mod_sub_distr_l_r: a:nat -> b:nat -> p:pos -> Lemma ((a - b) % p = (a - (b % p)) % p)
