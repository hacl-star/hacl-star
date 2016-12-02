module Hacl.Bignum.Predicates


(** Predicate associated to 'workable' bigintegers, restored after each bigint computation **)
val reduced_after_mul: h:mem -> b:felem -> GTot Type0
val reduced_before_mul_l: h:mem -> b:felem -> GTot Type0
val reduced_before_mul_r: h:mem -> b:felem -> GTot Type0
val reduced_wide: h:mem -> b:felem_wide -> GTot Type0

(** Predicate associated to 'workable' bigintegers, restored after each bigint computation **)
val reducible: h:mem -> b:felem -> GTot Type0

