module Vale.Math.Poly2.Galois
open FStar.Mul
module I = Lib.IntTypes
module G = Spec.GaloisField
module P = Vale.Math.Poly2_s
open Vale.Math.Poly2_s
open Vale.Math.Poly2
open FStar.Seq

(*
Connect Spec.GaloisField to Vale.Math.Poly2*
*)

val to_poly (#f:G.field) (e:G.felem f) : poly
val to_felem (f:G.field) (p:poly) : G.felem f

let irred_poly (f:G.field) : poly =
  let G.GF t irred = f in
  monomial (I.bits t) +. to_poly #f irred

unfold let min = FStar.Math.Lib.min
unfold let max = FStar.Math.Lib.max

unfold let ( &. ) = poly_and
unfold let ( |. ) = poly_or

val lemma_to_poly_degree (#f:G.field) (e:G.felem f) : Lemma
  (requires True)
  (ensures degree (to_poly e) < I.bits f.G.t)
  [SMTPat (to_poly e)]

val lemma_irred_degree (f:G.field) : Lemma
  (requires True)
  (ensures degree (irred_poly f) == I.bits f.G.t)
  [SMTPat (irred_poly f)]

val lemma_poly_felem (f:G.field) (p:poly) : Lemma
  (requires degree p < I.bits (G.GF?.t f))
  (ensures to_poly (to_felem f p) == p)
  [SMTPat (to_poly (to_felem f p))]

val lemma_felem_poly (#f:G.field) (e:G.felem f) : Lemma
  (requires True)
  (ensures to_felem f (to_poly e) == e)
  [SMTPat (to_felem f (to_poly e))]

val lemma_zero (f:G.field) : Lemma
  (requires True)
  (ensures to_poly #f G.zero == zero)
  [SMTPat (to_poly #f G.zero)]

val lemma_one (f:G.field) : Lemma
  (requires True)
  (ensures to_poly #f G.one == one)
  [SMTPat (to_poly #f G.one)]

val lemma_add (f:G.field) (e1 e2:G.felem f) : Lemma
  (requires True)
  (ensures to_poly (G.fadd e1 e2) == to_poly e1 +. to_poly e2)
  [SMTPat (to_poly (G.fadd e1 e2))]

val lemma_and (f:G.field) (e1 e2:G.felem f) : Lemma
  (requires True)
  (ensures to_poly (I.logand e1 e2) == (to_poly e1 &. to_poly e2))
  [SMTPat (to_poly (I.logand e1 e2))]

val lemma_or (f:G.field) (e1 e2:G.felem f) : Lemma
  (requires True)
  (ensures to_poly (I.logor e1 e2) == (to_poly e1 |. to_poly e2))
  [SMTPat (to_poly (I.logor e1 e2))]

val lemma_shift_left (f:G.field) (e:G.felem f) (n:I.shiftval f.G.t) : Lemma
  (requires True)
  (ensures to_poly (I.shift_left e n) == shift (to_poly e) (I.uint_v n) %. monomial (I.bits f.G.t))
  [SMTPat (to_poly (I.shift_left e n))]

val lemma_shift_right (f:G.field) (e:G.felem f) (n:I.shiftval f.G.t) : Lemma
  (requires True)
  (ensures to_poly (I.shift_right e n) == shift (to_poly e) (-(I.uint_v n)))
  [SMTPat (to_poly (I.shift_right e n))]

val lemma_mul (f:G.field) (a b:G.felem f) : Lemma
  (requires True)
  (ensures to_poly (G.fmul a b) == (to_poly a *. to_poly b) %. (irred_poly f))
  [SMTPat (to_poly (G.fmul a b))]
