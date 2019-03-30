module Fmul_inline

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

val fmul_inline
  (tmp:u512)
  (f1:u256)
  (out:u256) 
  (f2:u256)
  : Stack unit
    (requires fun h -> 
      adx_enabled /\ bmi2_enabled /\
      B.live h out /\ B.live h f1 /\ B.live h f2 /\ B.live h tmp /\
      (B.disjoint out f1 \/ out == f1) /\
      (B.disjoint out f2 \/ out == f2) /\
      (B.disjoint out tmp \/ out == tmp) /\
      (B.disjoint f1 f2 \/ f1 == f2) /\
      B.disjoint f1 tmp /\
      B.disjoint f2 tmp
    )
    (ensures  fun h0 _ h1 ->
      B.modifies (B.loc_union (B.loc_buffer out) (B.loc_buffer tmp)) h0 h1 /\
      (as_nat out h1) % prime == (as_nat f1 h0 * as_nat f2 h0) % prime)

val fmul2_inline
  (tmp:u1024)
  (f1:u512)
  (out:u512) 
  (f2:u512)
  : Stack unit
    (requires fun h -> 
      adx_enabled /\ bmi2_enabled /\
      B.live h out /\ B.live h f1 /\ B.live h f2 /\ B.live h tmp /\
      (B.disjoint out f1 \/ out == f1) /\
      (B.disjoint out f2 \/ out == f2) /\
      (B.disjoint out tmp \/ out == tmp) /\
      (B.disjoint f1 f2 \/ f1 == f2) /\
      B.disjoint f1 tmp /\
      B.disjoint f2 tmp
    )
    (ensures  fun h0 _ h1 ->
      B.modifies (B.loc_union (B.loc_buffer out) (B.loc_buffer tmp)) h0 h1 /\
     (let out0 = B.gsub out 0ul 4ul in
      let out1 = B.gsub out 4ul 4ul in
      let f10 = B.gsub f1 0ul 4ul in
      let f11 = B.gsub f1 4ul 4ul in
      let f20 = B.gsub f2 0ul 4ul in
      let f21 = B.gsub f2 4ul 4ul in
      (as_nat out0 h1) % prime == (as_nat f10 h0 * as_nat f20 h0) % prime /\
      (as_nat out1 h1) % prime == (as_nat f11 h0 * as_nat f21 h0) % prime))

val fmul1_inline
  (out:u256)
  (f1:u256) 
  (f2:UInt64.t{UInt64.v f2 < 131072})
  : Stack unit
    (requires fun h ->
      adx_enabled /\ bmi2_enabled /\
      B.live h out /\ B.live h f1 /\
      (B.disjoint out f1 \/ out == f1))
    (ensures  fun h0 _ h1 ->
      B.modifies (B.loc_buffer out) h0 h1 /\
      as_nat out h1 % prime == (as_nat f1 h0 * UInt64.v f2) % prime)
