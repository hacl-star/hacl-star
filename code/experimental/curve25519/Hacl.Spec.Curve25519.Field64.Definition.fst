module Hacl.Spec.Curve25519.Field64.Definition

open Lib.Sequence
open Lib.IntTypes

#reset-options "--z3rlimit 50  --using_facts_from '* -FStar.Seq'"

let felem4 = (uint64 * uint64 * uint64 * uint64)
let felem_wide4 = (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64)

open FStar.Mul

let prime:pos =
  assert_norm (pow2 255 - 19 > 0);
  pow2 255 - 19

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

let felem = x:nat{x < prime}
let feval (f:felem4) : GTot felem = (as_nat4 f) % prime
let feval_wide (f:felem_wide4) : GTot felem = (wide_as_nat4 f) % prime

val fadd: felem -> felem -> felem
let fadd f1 f2 = (f1 + f2) % prime

val fsub: felem -> felem -> felem
let fsub f1 f2 = (f1 - f2) % prime

val fmul: felem -> felem -> felem
let fmul f1 f2 = (f1 * f2) % prime

val fsqr: felem -> felem
let fsqr f1 = (f1 * f1) % prime
