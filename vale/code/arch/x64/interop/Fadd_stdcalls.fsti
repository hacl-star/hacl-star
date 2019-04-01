module Fadd_stdcalls

open X64.CPU_Features_s
open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
open Fast_defs
open FStar.Mul

unfold
let u256 = b:B.buffer UInt64.t{B.length b == 4}
unfold
let u512 = b:B.buffer UInt64.t{B.length b == 8}
unfold
let u1024 = b:B.buffer UInt64.t{B.length b == 16}

let as_nat (b:B.buffer UInt64.t{B.length b == 4}) (h:HS.mem) : GTot nat =
  let s = B.as_seq h b in
  let s0 = UInt64.v (Seq.index s 0) in
  let s1 = UInt64.v (Seq.index s 1) in
  let s2 = UInt64.v (Seq.index s 2) in
  let s3 = UInt64.v (Seq.index s 3) in
  pow2_four s0 s1 s2 s3

inline_for_extraction
val add1
  (out:u256)
  (f1:u256)
  (f2:UInt64.t)
  : Stack UInt64.t
  (requires fun h ->
    adx_enabled /\ bmi2_enabled /\
    B.live h out /\ B.live h f1 /\
    (B.disjoint out f1 \/ out == f1))
  (ensures fun h0 c h1 ->
    B.live h1 out /\ B.live h1 f1 /\
    B.modifies (B.loc_buffer out) h0 h1 /\
    as_nat out h1 + pow2_256 * UInt64.v c == as_nat f1 h0 + UInt64.v f2)  

inline_for_extraction
val fadd
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
      (as_nat out h1) % prime == (as_nat f1 h0 + as_nat f2 h0) % prime)
