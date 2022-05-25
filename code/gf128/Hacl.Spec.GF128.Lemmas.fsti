module Hacl.Spec.GF128.Lemmas

open FStar.Mul
open Spec.GaloisField

module S = Spec.GF128


#set-options "--z3rlimit 30 --max_fuel 0 --max_ifuel 0"

let elem = S.elem
let zero : elem = zero
let one : elem = one

let ( +% ) (a b:elem) : elem = fadd #S.gf128 a b
let ( *% ) (a b:elem) : elem = fmul_be #S.gf128 a b

val add_identity: a:elem -> Lemma (zero +% a == a)

val mul_identity: a:elem -> Lemma (one *% a == a)

val add_associativity: a:elem -> b:elem -> c:elem ->
  Lemma (a +% b +% c == a +% (b +% c))

val add_commutativity: a:elem -> b:elem -> Lemma (a +% b == b +% a)

val mul_associativity: a:elem -> b:elem -> c:elem ->
  Lemma (a *% b *% c == a *% (b *% c))

val mul_commutativity: a:elem -> b:elem -> Lemma (a *% b == b *% a)



val gf128_update_multi_mul_add_lemma_load_acc_aux:
    a0:elem -> b0:elem -> b1:elem -> b2:elem -> b3:elem
  -> r:elem ->
  Lemma
  ((a0 +% b0) *% (r *% (r *% (r *% r))) +% (zero +% b1) *% (r *% (r *% r)) +%
   (zero +% b2) *% (r *% r) +% (zero +% b3) *% r ==
  ((((a0 +% b0) *% r +% b1) *% r +% b2) *% r +% b3) *% r)


val gf128_update_multi_mul_add_lemma_loop_aux:
    a0:elem -> a1:elem -> a2:elem -> a3:elem
  -> b0:elem -> b1:elem -> b2:elem -> b3:elem
  -> r:elem ->
  Lemma
   ((a0 *% (r *% (r *% (r *% r))) +% b0) *% (r *% (r *% (r *% r))) +%
    (a1 *% (r *% (r *% (r *% r))) +% b1) *% (r *% (r *% r)) +%
    (a2 *% (r *% (r *% (r *% r))) +% b2) *% (r *% r) +%
    (a3 *% (r *% (r *% (r *% r))) +% b3) *% r ==
    ((((a0 *% (r *% (r *% (r *% r))) +%
        a1 *% (r *% (r *% r)) +%
	a2 *% (r *% r) +%
	a3 *% r +% b0) *% r +% b1) *% r +% b2) *% r +% b3) *% r)


open Lib.Sequence
open Lib.IntTypes

let elem_s = lseq uint64 2

let to_elem (x:elem_s) : elem =
  mk_int #U128 (v x.[0] + v x.[1] * pow2 64)

let logxor_s (x:elem_s) (y:elem_s) : elem_s =
  let r0 = x.[0] ^. y.[0] in
  let r1 = x.[1] ^. y.[1] in
  Lib.Sequence.create2 r0 r1

val logxor_s_lemma: x:elem_s -> y:elem_s -> Lemma
  (to_elem (logxor_s x y) == to_elem x ^. to_elem y)

let logand_s (x:elem_s) (y:elem_s) : elem_s =
  let r0 = x.[0] &. y.[0] in
  let r1 = x.[1] &. y.[1] in
  Lib.Sequence.create2 r0 r1

val logand_s_lemma: x:elem_s -> y:elem_s -> Lemma
  (to_elem (logand_s x y) == (to_elem x &. to_elem y))
