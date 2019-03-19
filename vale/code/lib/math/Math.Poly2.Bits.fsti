module Math.Poly2.Bits
open Words_s
open Types_s
open FStar.UInt
open FStar.Seq
open Arch.Types
open Math.Poly2_s
open Math.Poly2.Bits_s
open Math.Poly2
open Math.Poly2.Lemmas

val of_nat32 (n:nat32) : p:poly{degree p < 32}

val of_nat32_zero : _:unit{of_nat32 0 == zero}

val of_nat32_xor (a b:nat32) : Lemma
  (of_nat32 a +. of_nat32 b == of_nat32 (ixor a b))

let poly128_of_poly32s (a0 a1 a2 a3:poly) : poly =
  a0 +. shift a1 32 +. shift a2 64 +. shift a3 96

let poly128_of_nat32s (a0 a1 a2 a3:nat32) : poly =
  poly128_of_poly32s (of_nat32 a0) (of_nat32 a1) (of_nat32 a2) (of_nat32 a3)

val lemma_quad32_of_nat32s (a0 a1 a2 a3:nat32) : Lemma
  (Mkfour a0 a1 a2 a3 == to_quad32 (poly128_of_nat32s a0 a1 a2 a3))

val lemma_quad32_to_nat32s (a:poly) : Lemma
  (requires degree a <= 127)
  (ensures (
    let Mkfour a0 a1 a2 a3 = to_quad32 a in
    a == poly128_of_nat32s a0 a1 a2 a3
  ))

val lemma_quad32_double (a:poly) : Lemma
  (requires degree a <= 127)
  (ensures
    of_double32 (quad32_double_lo (to_quad32 a)) == a %. monomial 64 /\
    of_double32 (quad32_double_hi (to_quad32 a)) == a /. monomial 64 /\
    a == (a /. monomial 64) *. monomial 64 +. a %. monomial 64 /\
    (a /. monomial 64) *. monomial 64 == shift (a /. monomial 64) 64
  )

val lemma_of_double32_degree (d:double32) : Lemma
  (degree (of_double32 d) < 64)
  [SMTPat (degree (of_double32 d))]

val lemma_of_quad32_degree (q:quad32) : Lemma
  (degree (of_quad32 q) < 128)
  [SMTPat (degree (of_quad32 q))]

val lemma_to_of_quad32 (q:quad32) : Lemma (to_quad32 (of_quad32 q) == q)

val lemma_of_to_quad32 (a:poly) : Lemma
  (requires degree a < 128)
  (ensures of_quad32 (to_quad32 a) == a)

