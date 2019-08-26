module Hacl.Spec.GF128.Lemmas

open FStar.Mul
open Spec.GaloisField

module S = Spec.GF128


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let elem = S.elem

let ( +% ) (a b:elem) : elem = fadd #S.gf128 a b
let ( *% ) (a b:elem) : elem = fmul_be #S.gf128 a b

val add_identity: a:elem -> Lemma (zero +% a == a)
let add_identity a = admit()

val add_commutativity: a:elem -> b:elem -> Lemma (a +% b == b +% a)
let add_commutativity a b = admit()


val gf128_update_multi_mul_add_lemma_load_acc_aux:
    a0:elem -> b0:elem -> b1:elem -> b2:elem -> b3:elem
  -> r:elem -> r2:elem{r2 == r *% r} -> r3:elem{r3 == r *% r2} -> r4:elem{r4 == r *% r3} ->
  Lemma
  ((a0 +% b0) *% r4 +% (zero +% b1) *% r3 +% (zero +% b2)*% r2 +% (zero +% b3) *% r ==
  ((((a0 +% b0) *% r +% b1) *% r +% b2) *% r +% b3) *% r)

let gf128_update_multi_mul_add_lemma_load_acc_aux a0 b0 b1 b2 b3 r r2 r3 r4 = admit()


val gf128_update_multi_mul_add_lemma_loop_aux:
    a0:elem -> a1:elem -> a2:elem -> a3:elem
  -> b0:elem -> b1:elem -> b2:elem -> b3:elem
  -> r:elem -> r2:elem{r2 == r *% r} -> r3:elem{r3 == r *% r2} -> r4:elem{r4 == r *% r3} ->
  Lemma
  ((a0 *% r4 +% b0) *% r4 +% (a1 *% r4 +% b1) *% r3 +% (a2 *% r4 +% b2) *% r2 +% (a3 *% r4 +% b3) *% r ==
  ((((a0 *% r4 +% a1 *% r3 +% a2 *% r2 +% a3 *% r +% b0) *% r +% b1) *% r +% b2) *% r +% b3) *% r)

let gf128_update_multi_mul_add_lemma_loop_aux a0 a1 a2 a3 b0 b1 b2 b3 r r2 r3 r4 = admit()
