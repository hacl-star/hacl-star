module Math.Poly2.Words
open Words_s
open Words.Four_s
open Types_s
open FStar.UInt
open FStar.Seq
open Arch.Types
open Math.Poly2_s
open Math.Poly2.Bits_s
open Math.Poly2
open Math.Poly2.Lemmas
open Math.Poly2.Bits

val lemma_quad32_zero (_:unit) : Lemma
  (of_quad32 (Mkfour 0 0 0 0) == zero /\ Mkfour 0 0 0 0 == to_quad32 zero)

val lemma_quad32_ones (_:unit) : Lemma
  (let q = Mkfour 0xffffffff 0xffffffff 0xffffffff 0xffffffff in of_quad32 q == ones 128 /\ q == to_quad32 (ones 128))

val lemma_add128 (a b:poly) : Lemma
  (requires degree a <= 127 /\ degree b <= 127)
  (ensures to_quad32 (a +. b) == quad32_xor (to_quad32 a) (to_quad32 b))

val lemma_add_quad32 (a b:quad32) : Lemma
  (ensures of_quad32 a +. of_quad32 b == of_quad32 (quad32_xor a b))

val lemma_and128 (a b:poly) : Lemma
  (requires degree a <= 127 /\ degree b <= 127)
  (ensures to_quad32 (poly_and a b) == (four_map2 (fun di si -> iand di si) (to_quad32 a) (to_quad32 b)))

val lemma_and_quad32 (a b:quad32) : Lemma
  (ensures poly_and (of_quad32 a) (of_quad32 b) == of_quad32 (four_map2 (fun di si -> iand di si) a b))

val lemma_quad32_double_shift (a:poly) : Lemma
  (requires degree a <= 127)
  (ensures (
    let Mkfour q0 q1 q2 q3 = to_quad32 a in
    Mkfour #nat32 0 0 q0 q1 == to_quad32 ((a %. monomial 64) *. monomial 64) /\
    Mkfour #nat32 q2 q3 0 0 == to_quad32 (a /. monomial 64)
  ))

val lemma_quad32_double_swap (a:poly) : Lemma
  (requires degree a <= 127)
  (ensures (
    let Mkfour q0 q1 q2 q3 = to_quad32 a in
    to_quad32 (swap a 64) == Mkfour q2 q3 q0 q1
  ))

