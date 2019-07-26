module Hacl.Spec.Ed25519.Field56.Definition

open Lib.Sequence
open Lib.IntTypes

#reset-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"

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
   uint_v s0 +
   0x100000000000000 * uint_v s1 +
   0x10000000000000000000000000000 * uint_v s2 +
   0x1000000000000000000000000000000000000000000 * uint_v s3 +
   0x100000000000000000000000000000000000000000000000000000000 * uint_v s4

noextract
let felem_fits (f:felem5) (s:nat & nat & nat & nat & nat) =
  let (s0, s1, s2, s3, s4) = f in
  let (m0, m1, m2, m3, m4) = s in
  uint_v s0 <= m0 * pow56 /\
  uint_v s1 <= m1 * pow56 /\
  uint_v s2 <= m2 * pow56 /\
  uint_v s3 <= m3 * pow56 /\
  uint_v s4 <= m4 * pow56
