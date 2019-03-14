module Spec.CTR.Lemmas

module ST = FStar.HyperStack.ST

open FStar.Mul

#set-options "--max_fuel 0 --initial_fuel 0"

val lemma_div: a:nat -> b:pos{a >= b} -> Lemma ((a-b)/b = a / b - 1)
let lemma_div a b =
  Math.Lemmas.lemma_div_mod a b;
  Math.Lemmas.lemma_div_mod (a-b) b;
  Math.Lemmas.lemma_mod_plus (a - b) 1 b
