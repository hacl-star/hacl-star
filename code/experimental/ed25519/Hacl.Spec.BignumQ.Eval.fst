module Hacl.Spec.BignumQ.Eval

open FStar.Mul
open FStar.Seq
open FStar.UInt64

let op_String_Access = Seq.index
let op_String_Assignment = Seq.upd

#reset-options "--max_fuel 0 --max_ifuel 0"

let qelem = s:seq FStar.UInt64.t{length s == 5}
let u32 = FStar.UInt32.t
let u64 = FStar.UInt64.t

let p1 = 0x100000000000000
let p2 = 0x10000000000000000000000000000
let p3 = 0x1000000000000000000000000000000000000000000
let p4 = 0x100000000000000000000000000000000000000000000000000000000

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
