module Hacl.Bignum.Predicates


open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters


type sfelem      = Seq.seq limb
type sfelem_wide = Seq.seq wide


let is_sum h1 (a:felem) h0 (b:felem) : GTot Type0 =
  live h1 a /\ live h0 a /\ live h0 b
  /\ (forall (i:nat). {:pattern (v (get h1 a i))} i < len ==> v (get h1 a i) = v (get h0 a i) + v (get h0 b i))


let 

let is_difference h1 (a:felem) h0 (b:felem) : GTot Type0 =
  live h1 a /\ live h0 a /\ live h0 b
  /\ (forall (i:nat). {:pattern (v (get h1 a i))} i < len ==>
      v (get h1 a i) = v (get h0 b i) - v (get h0 b i))


let is_sum_scalar_multiplication h1 a h0 b s 

let is_multiplication hc c ha a hb b : GTot Type0 =
  live hc c /\ live ha a /\ live hb b
  /\ 
let fsum_spec ha (a:felem) hb (b:felem)


(** Predicate associated to 'workable' bigintegers, restored after each bigint computation **)
val reduced_after_mul: h:mem -> b:felem -> GTot Type0
val reduced_before_mul_l: h:mem -> b:felem -> GTot Type0
val reduced_before_mul_r: h:mem -> b:felem -> GTot Type0
val reduced_wide: h:mem -> b:felem_wide -> GTot Type0

(** Predicate associated to 'workable' bigintegers, restored after each bigint computation **)
val reducible: h:mem -> b:felem -> GTot Type0

