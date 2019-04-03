module Fsqr_inline

open X64.CPU_Features_s
open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
open Fast_defs
open FStar.Mul
open Fadd_stdcalls

val fsqr_inline
  (tmp:u512)
  (f1:u256)
  (out:u256)
  : Stack unit
    (requires fun h -> 
    adx_enabled /\ bmi2_enabled /\
    B.live h out /\ B.live h f1 /\ B.live h tmp /\
    (B.disjoint out f1 \/ out == f1) /\
    (B.disjoint out tmp \/ out == tmp) /\
    B.disjoint f1 tmp
    )
    (ensures  fun h0 _ h1 ->
      B.modifies (B.loc_union (B.loc_buffer out) (B.loc_buffer tmp)) h0 h1 /\
      (as_nat out h1) % prime == (as_nat f1 h0 * as_nat f1 h0) % prime)

val fsqr2_inline
  (tmp:u1024)
  (f1:u512)
  (out:u512) 
  : Stack unit
    (requires fun h -> 
      adx_enabled /\ bmi2_enabled /\
      B.live h out /\ B.live h f1 /\ B.live h tmp /\
      (B.disjoint out f1 \/ out == f1) /\
      (B.disjoint out tmp \/ out == tmp) /\
      B.disjoint f1 tmp
    )
    (ensures  fun h0 _ h1 ->
      B.modifies (B.loc_union (B.loc_buffer out) (B.loc_buffer tmp)) h0 h1 /\
     (let out0 = B.gsub out 0ul 4ul in
      let out1 = B.gsub out 4ul 4ul in
      let f10 = B.gsub f1 0ul 4ul in
      let f11 = B.gsub f1 4ul 4ul in
      (as_nat out0 h1) % prime == (as_nat f10 h0 * as_nat f10 h0) % prime /\
      (as_nat out1 h1) % prime == (as_nat f11 h0 * as_nat f11 h0) % prime))
