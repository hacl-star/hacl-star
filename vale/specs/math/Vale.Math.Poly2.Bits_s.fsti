module Vale.Math.Poly2.Bits_s
open FStar.Mul
open Vale.Def.Words_s
open Vale.Def.Types_s
open Vale.Math.Poly2_s
open FStar.Seq
open FStar.UInt

// Bit-level representations of poly, expressed in terms of FStar.UInt.uint_t.
// Least-significant bit represents x^0, next bit represents x^1, etc.
// (Note that FStar.UInt uses 0 for most-significant bit,
// so definitions below use "reverse" to compensate.)

let to_uint (n:pos) (a:poly) : uint_t n =
  from_vec #n (to_seq (reverse a (n - 1)) n)

let of_uint (n:pos) (u:uint_t n) : poly =
  reverse (of_seq (to_vec #n u)) (n - 1)

let to_double32_def (a:poly) : double32 =
  let s = to_seq (reverse a 63) 64 in
  Mktwo
    (from_vec #32 (slice s 32 64)) // lo word contains a.[31] .. a.[0]
    (from_vec #32 (slice s 0 32)) // hi word contains a.[63] .. a.[32]

let of_double32_def (d:double32) : poly =
  let Mktwo d0 d1 = d in
  let s = (append (
    (to_vec #32 d1))
    (to_vec #32 d0))
    in
  reverse (of_seq s) 63

let to_quad32_def (a:poly) : quad32 =
  let s = to_seq (reverse a 127) 128 in
  Mkfour
    (from_vec #32 (slice s 96 128)) // lo word contains a.[31] .. a.[0]
    (from_vec #32 (slice s 64 96))
    (from_vec #32 (slice s 32 64))
    (from_vec #32 (slice s 0 32)) // hi word contains a.[127] .. a.[96]

let of_quad32_def (q:quad32) : poly =
  let Mkfour q0 q1 q2 q3 = q in
  let s = (append (append (append (
    (to_vec #32 q3))
    (to_vec #32 q2))
    (to_vec #32 q1))
    (to_vec #32 q0))
    in
  reverse (of_seq s) 127

val to_double32 (a:poly) : double32
val of_double32 (q:double32) : poly
val to_quad32 (a:poly) : quad32
val of_quad32 (q:quad32) : poly

val reveal_to_double32 (a:poly) : Lemma (to_double32 a == to_double32_def a)
val reveal_of_double32 (d:double32) : Lemma (of_double32 d == of_double32_def d)
val reveal_to_quad32 (a:poly) : Lemma (to_quad32 a == to_quad32_def a)
val reveal_of_quad32 (q:quad32) : Lemma (of_quad32 q == of_quad32_def q)
