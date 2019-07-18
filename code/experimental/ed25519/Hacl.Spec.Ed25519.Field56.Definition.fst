module Hacl.Spec.Ed25519.Field56.Definition

open Lib.Sequence
open Lib.IntTypes

#reset-options "--z3rlimit 20"

let felem5 = (uint64 * uint64 * uint64 * uint64 * uint64)

abstract
let pow32: (pow32: pos { pow32 == pow2 32 }) =
  let pow32: pos = normalize_term (pow2 32) in
  assert_norm (pow32 == pow2 32);
  pow32


abstract
let pow56: (pow56: pos { pow56 == pow2 56 }) =
  let pow56: pos = normalize_term (pow2 56) in
  assert_norm (pow56 == pow2 56);
  pow56

open FStar.Mul

noextract
val as_nat5: f:felem5 -> GTot nat
let as_nat5 f =
  let (s0, s1, s2, s3, s4) = f in
   (uint_v s0 % pow56) +
   (uint_v s1 % pow56) * pow56 +
   (uint_v s2 % pow56) * pow56 * pow56 +
   (uint_v s3 % pow56) * pow56 * pow56 * pow56 +
   (uint_v s4 % pow32) * pow56 * pow56 * pow56 * pow56
