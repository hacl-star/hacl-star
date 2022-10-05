module Vale.PPC64LE.Vecs
// This interface should not refer to Semantics_s

open Vale.Def.Prop_s
open Vale.PPC64LE.Machine_s

type t = vecs_t

val equal (vecs1:t) (vecs2:t) : prop0

val lemma_equal_intro (vecs1:t) (vecs2:t) : Lemma
  (requires forall (x:vec). vecs1 x == vecs2 x)
  (ensures equal vecs1 vecs2)
  [SMTPat (equal vecs1 vecs2)]

val lemma_equal_elim (vecs1:t) (vecs2:t) : Lemma
  (requires equal vecs1 vecs2)
  (ensures vecs1 == vecs2)
  [SMTPat (equal vecs1 vecs2)]

