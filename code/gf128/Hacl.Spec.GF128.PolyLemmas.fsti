module Hacl.Spec.GF128.PolyLemmas

open FStar.Mul

open Lib.IntTypes
open Lib.IntVector

open Vale.Math.Poly2_s
open Vale.Math.Poly2
open Vale.Math.Poly2.Bits_s
open Vale.Math.Poly2.Lemmas

open Hacl.Spec.GF128.Poly_s

val lemma_of_to_uint_128 (a:poly) : Lemma
  (requires degree a < 128)
  (ensures of_uint 128 (to_uint 128 a) == a)
  [SMTPat (of_uint 128 (to_uint 128 a))]

val lemma_to_of_vec128 (q:vec128) : Lemma
  (ensures to_vec128 (of_vec128 q) == q)
  [SMTPat (to_vec128 (of_vec128 q))]

val lemma_of_to_vec128 (a:poly) : Lemma
  (requires degree a < 128)
  (ensures of_vec128 (to_vec128 a) == a)
  [SMTPat (of_vec128 (to_vec128 a))]

val lemma_vec128_zero (_:unit) : Lemma
  (of_vec128 (uint_to_vec128 0) == zero /\ uint_to_vec128 0 == to_vec128 zero)

val lemma_vec128_ones (_:unit) : Lemma
  (let q = (uint_to_vec128 0xffffffffffffffffffffffffffffffff) in
    of_vec128 q == ones 128 /\ q == to_vec128 (ones 128))

val lemma_add128 (a b:poly) : Lemma
  (requires degree a <= 127 /\ degree b <= 127)
  (ensures to_vec128 (add a b) == to_vec128 a ^| to_vec128 b)

val lemma_add_vec128 (a b:vec128) : Lemma
  (ensures add (of_vec128 a) (of_vec128 b) == of_vec128 (a ^| b))

val lemma_and128 (a b:poly) : Lemma
  (requires degree a <= 127 /\ degree b <= 127)
  (ensures to_vec128 (poly_and a b) == (to_vec128 a &| to_vec128 b))

val lemma_and_vec128 (a b:vec128) : Lemma
  (ensures poly_and (of_vec128 a) (of_vec128 b) == of_vec128 (a &| b))

val lemma_vec128_double_shift (a:poly) : Lemma
  (requires degree a <= 127)
  (ensures (
    let q = to_vec128 a in
    q <<| 64ul == to_vec128 (mul (mod a (monomial 64)) (monomial 64)) /\
    q >>| 64ul == to_vec128 (div a (monomial 64))
  ))

val lemma_vec128_shift_left_64 (p:vec128) (s:shiftval U64) : Lemma
  (ensures (
    let n = monomial 64 in
    let a = of_vec128 p in
    let a0 = mod (shift (mod a n) (v s)) n in
    let a1 = mod (shift (div a n) (v s)) n in
    cast U128 1 (vec_shift_left (cast U64 2 p) s) ==
      to_vec128 (add (shift a1 64) a0)
  ))

val lemma_vec128_shift_right_64 (p:vec128) (s:shiftval U64) : Lemma
  (ensures (
    let n = monomial 64 in
    let a = of_vec128 p in
    let a0 = shift (mod a n) (-(v s)) in
    let a1 = shift (div a n) (-(v s)) in
    cast U128 1 (vec_shift_right (cast U64 2 p) s) ==
      to_vec128 (add (shift a1 64) a0)
  ))
