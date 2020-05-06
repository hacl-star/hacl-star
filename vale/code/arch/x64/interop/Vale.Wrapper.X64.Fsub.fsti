module Vale.Wrapper.X64.Fsub

open Vale.X64.CPU_Features_s
open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
open Vale.Curve25519.Fast_defs
open FStar.Mul
open Vale.Wrapper.X64.Fadd

inline_for_extraction
val fsub_e
  (out:u256)
  (f1:u256)
  (f2:u256)
  : Stack unit
    (requires fun h ->
      adx_enabled /\ bmi2_enabled /\
      B.live h f1 /\ B.live h f2 /\ B.live h out /\
      (B.disjoint out f1 \/ out == f1) /\
      (B.disjoint out f2 \/ out == f2) /\
      (B.disjoint f1 f2 \/ f1 == f2))
    (ensures  fun h0 _ h1 ->
      B.modifies (B.loc_buffer out) h0 h1 /\
      (as_nat out h1) % prime == (as_nat f1 h0 - as_nat f2 h0) % prime)
