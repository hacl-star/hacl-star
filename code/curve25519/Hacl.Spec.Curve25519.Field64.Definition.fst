module Hacl.Spec.Curve25519.Field64.Definition

open Lib.Sequence
open Lib.IntTypes

module P = Spec.Curve25519

#reset-options "--z3rlimit 50  --using_facts_from '* -FStar.Seq'"

let felem4 = (uint64 * uint64 * uint64 * uint64)
let felem_wide4 = (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64)

open FStar.Mul

noextract
val as_nat4: f:felem4 -> GTot nat
let as_nat4 f =
  let (s0, s1, s2, s3) = f in
  v s0 + v s1 * pow2 64 + v s2 * pow2 64 * pow2 64 +
  v s3 * pow2 64 * pow2 64 * pow2 64

noextract
val wide_as_nat4: f:felem_wide4 -> GTot nat
let wide_as_nat4 f =
  let (s0, s1, s2, s3, s4, s5, s6, s7) = f in
  v s0 + v s1 * pow2 64 + v s2 * pow2 64 * pow2 64 +
  v s3 * pow2 64 * pow2 64 * pow2 64 +
  v s4 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s5 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s6 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s7 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64

let feval (f:felem4) : GTot P.elem = (as_nat4 f) % P.prime
let feval_wide (f:felem_wide4) : GTot P.elem = (wide_as_nat4 f) % P.prime
