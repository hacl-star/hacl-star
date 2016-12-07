module Hacl.Bignum.Predicates


open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters


#set-options "--lax"


(** Predicate associated to 'workable' bigintegers, restored after each bigint computation **)
let reduced_after_mul h b = admit()
let reduced_before_mul_l h b = admit()
let reduced_before_mul_r h b = admit()
let reduced_wide h b = admit()

(** Predicate associated to 'workable' bigintegers, restored after each bigint computation **)
let reducible h b = admit()

let lemma_sum_to_mul h1 a h0 b = admit()
let lemma_difference_to_mul h1 a b0 b = admit()
