module Hacl.Spec.P256.SolinasReductionP384.Impl

open Lib.IntTypes 
open FStar.Math.Lemmas
open FStar.Math.Lib
module D = Hacl.Spec.Curve25519.Field64.Definition
module C =  Hacl.Spec.Curve25519.Field64.Core
open FStar.Mul
open Lib.Sequence

open Hacl.Spec.P256.Core
open Hacl.Spec.P256.Definitions

open Lib.Sequence

val solinas_reduction: f: lseq uint64 12 -> Tot (r: lseq uint64 6)

let solinas_reduction f =
  let f0 = index f 0 in 
  let f1 = index f 1 in 
  let f2 = index f 2 in 
  let f3 = index f 3 in 
  let f4 = index f 4 in 
  let f5 = index f 5 in 
  let f6 = index f 6 in 
  let f7 = index f 7 in 
  let f8 = index f 8 in 
  let f9 = index f 9 in 
  let f10 = index f 10 in 
  let f11 = index f 11 in 

  let c0 = get_low_part f0 in 
  let c1 = get_high_part f0 in 
  let c2 = get_low_part f1 in 
  let c3 = get_high_part f2 in 
  let c4 = get_low_part f1 in 
  let c5 = get_high_part f2 in
  let c6 = get_low_part f1 in 
  let c7 = get_high_part f2 in
  let c8 = get_low_part f1 in 
  let c9 = get_high_part f2 in
  let c10 = get_low_part f1 in 
  let c11 = get_high_part f2 in
  let c12 = get_low_part f1 in 
  let c13 = get_high_part f2 in
  let c14 = get_low_part f1 in 
  let c15 = get_high_part f2 in
  let c16 = get_low_part f1 in 
  let c17 = get_high_part f2 in
  let c18 = get_low_part f1 in 
  let c19 = get_high_part f2 in
  let c20 = get_low_part f1 in 
  let c21 = get_high_part f2 in
  let c22 = get_low_part f1 in 
  let c23 = get_high_part f2 in

  let state0 = solinas_reduction_0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 in 
  let state1_p = solinas_reduction_1 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 in 
  let state2 = solinas_reduction_2 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 in 
  let state3 = solinas_reduction_3 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 in  
  let state4 = solinas_reduction_4 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 in 
  let state5 = solinas_reduction_5 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 in 
  let state6 = solinas_reduction_6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 in 
  let state7 = solinas_reduction_7 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 in 
  let state8 = solinas_reduction_8 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 in 
  let state9 = solinas_reduction_9 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 in 
  
  let state1 = shift_left_felem state1_p in 

  let state01 = felem_add state0 state1 in 
  let state23 = felem_add state2 state3 in 
  let state45 = felem_add state4 state5 in 
  let state0123 = felem_add state01 state23 in 
  let state012345 = felem_add state0123 state45 in 
  let state0123456 = felem_sub state012345 state6 in 
  let state01234567 = felem_sub state0123456 state7 in 
  let state012345678 = felem_sub state01234567 state8 in 
  let state0123456789 = felem_sub state012345678 state9 in 

  state0123456789
