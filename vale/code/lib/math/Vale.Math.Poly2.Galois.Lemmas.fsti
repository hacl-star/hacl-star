module Vale.Math.Poly2.Galois.Lemmas
open FStar.Mul
module I = Lib.IntTypes
module G = Spec.GaloisField
module P = Vale.Math.Poly2_s
open Vale.Math.Poly2_s
open Vale.Math.Poly2
open Vale.Math.Poly2.Galois

unfold let fadd (#f:G.field) (a b:G.felem f) = G.fadd #f a b
unfold let fmul (#f:G.field) (a b:G.felem f) = G.fmul #f a b

val lemma_eq_to_poly (#f:G.field) (a b:G.felem f) : Lemma
  (requires to_poly a == to_poly b)
  (ensures a == b)

val lemma_mul_zero (#f:G.field) (a:G.felem f) : Lemma (fmul a G.zero == G.zero)
val lemma_mul_one (#f:G.field) (a:G.felem f) : Lemma (fmul a G.one == a)

val lemma_mul_commute (#f:G.field) (a b:G.felem f) : Lemma
  (fmul a b == fmul b a)

val lemma_mul_associate (#f:G.field) (a b c:G.felem f) : Lemma
  (fmul a (fmul b c) == fmul (fmul a b) c)

val lemma_mul_distribute_left (#f:G.field) (a b c:G.felem f) : Lemma
  (fmul (fadd a b) c == fadd (fmul a c) (fmul b c))

val lemma_mul_distribute_right (#f:G.field) (a b c:G.felem f) : Lemma
  (fmul a (fadd b c) == fadd (fmul a b) (fmul a c))
