module Vale.PPC64LE.Vecs
open Vale.PPC64LE.Machine_s
open FStar.FunctionalExtensionality

let equal vecs1 vecs2 = feq vecs1 vecs2
let lemma_equal_intro vecs1 vecs2 = ()
let lemma_equal_elim vecs1 vecs2 = ()

