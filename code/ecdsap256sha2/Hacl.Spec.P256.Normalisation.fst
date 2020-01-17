module Hacl.Spec.P256.Normalisation

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Definitions
open Hacl.Spec.P256.MontgomeryMultiplication
open Hacl.Spec.P256
open Hacl.Spec.P256.Lemmas

open FStar.Math.Lemmas

let prime = prime256


open FStar.Mul  
#reset-options "--z3refresh --z3rlimit 300" 
val lemma_norm_as_specification: xD: nat -> yD: nat -> zD: nat -> 
  x3 : nat {x3 == xD * (pow (zD * zD) (prime-2) % prime) % prime}-> 
  y3 : nat {y3 == yD * (pow (zD * zD * zD) (prime -2) % prime) % prime} -> 
  z3: nat {if isPointAtInfinity(xD, yD, zD) then z3 == 0 else z3 == 1} -> 
    Lemma (let (xN, yN, zN) = _norm (xD, yD, zD) in 
  x3 == xN /\ y3 == yN /\ z3 == zN)


let lemma_norm_as_specification xD yD zD x3 y3 z3 = 
  power_distributivity (zD * zD * zD) (prime - 2) prime;
  power_distributivity (zD * zD) (prime -2) prime