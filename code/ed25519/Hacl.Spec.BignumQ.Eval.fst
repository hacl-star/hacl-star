module Hacl.Spec.BignumQ.Eval

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.Seq
open FStar.UInt64

let op_String_Access = Seq.index
let op_String_Assignment = Seq.upd

#reset-options "--max_fuel 0"

let qelem = s:seq FStar.UInt64.t{length s == 5}
let u32 = FStar.UInt32.t
let u64 = FStar.UInt64.t

let p1 = 0x100000000000000
let p2 = 0x10000000000000000000000000000
let p3 = 0x1000000000000000000000000000000000000000000
let p4 = 0x100000000000000000000000000000000000000000000000000000000
let p5 = 0x10000000000000000000000000000000000000000000000000000000000000000000000
let p6 = 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000
let p7 = 0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
let p8 = 0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
let p9 = 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

let eval_q (s:qelem) : Tot nat =
  v (s.[0]) + p1 * v (s.[1]) + p2 * v (s.[2]) + p3 * v (s.[3]) + p4 * v (s.[4])

let eval_q_2 s0 s1 : Tot nat =
  v s0 + p1 * v s1

let eval_q_3 s0 s1 s2 : Tot nat =
  v (s0) + p1 * v (s1) + p2 * v (s2)

let eval_q_4 s0 s1 s2 s3 : Tot nat =
  v (s0) + p1 * v (s1) + p2 * v (s2) + p3 * v (s3)

let eval_q_5 s0 s1 s2 s3 s4 : Tot nat =
  v (s0) + p1 * v (s1) + p2 * v (s2) + p3 * v (s3) + p4 * v (s4)

let eval_q_6 s0 s1 s2 s3 s4 s5 : Tot nat =
  v (s0) + p1 * v (s1) + p2 * v (s2) + p3 * v (s3) + p4 * v (s4) + p5 * v s5

let eval_q_10 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : Tot nat =
  v (s0) + p1 * v (s1) + p2 * v (s2) + p3 * v (s3) + p4 * v (s4)
  + p5 * v (s5) + p6 * v (s6) + p7 * v (s7) + p8 * v (s8) + p9 * v (s9)

let eval_q_wide t0 t1 t2 t3 t4 t5 t6 t7 t8 =
  UInt128.v t0 + p1 * UInt128.v (t1) + p2 * UInt128.v (t2) + p3 * UInt128.v (t3) + p4 * UInt128.v (t4)
  + p5 * UInt128.v t5 + p6 * UInt128.v t6 + p7 * UInt128.v t7 + p8 * UInt128.v t8
