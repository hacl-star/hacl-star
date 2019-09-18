module Hacl.Spec.BignumQ.Definitions

open FStar.Mul
open Lib.IntTypes

module S = Spec.Ed25519

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let qelem5 = (uint64 & uint64 & uint64 & uint64 & uint64)
let qelem_wide5 = (uint64 & uint64 & uint64 & uint64 & uint64 & uint64 & uint64 & uint64 & uint64 & uint64)

//abstract
let pow56: (pow56:pos {pow2 64 == 256 * pow56 /\ pow56 == pow2 56}) =
  let pow56: pos = normalize_term (pow2 56) in
  assert_norm (pow56 > 0);
  assert_norm (pow56 == pow2 56);
  assert_norm (pow2 64 == 256 * pow56);
  assert_norm (pow2 128 == 65536 * pow56 * pow56);
  pow56


let pow112: (pow112:pos {pow112 == pow2 112}) = normalize_term (pow2 112)
let pow168: (pow168:pos {pow168 == pow2 168}) = normalize_term (pow2 168)
let pow224: (pow224:pos {pow224 == pow2 224}) = normalize_term (pow2 224)
let pow280: (pow280:pos {pow280 == pow2 280}) = normalize_term (pow2 280)
let pow336: (pow336:pos {pow336 == pow2 336}) = normalize_term (pow2 336)
let pow392: (pow392:pos {pow392 == pow2 392}) = normalize_term (pow2 392)
let pow448: (pow448:pos {pow448 == pow2 448}) = normalize_term (pow2 448)
let pow504: (pow504:pos {pow504 == pow2 504}) = normalize_term (pow2 504)


let scale64 = s:nat{s <= 256}
let nat5 = (nat & nat & nat & nat & nat)
let nat10 = (nat & nat & nat & nat & nat & nat & nat & nat & nat & nat)

let scale64_5 = x:nat5{let (x1,x2,x3,x4,x5) = x in
		       x1 <= 256 /\ x2 <= 256 /\ x3 <= 256 /\ x4 <= 256 /\ x5 <= 256}

let scale64_10 = x:nat10{let (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) = x in
                       x1 <= 256 /\ x2 <= 256 /\ x3 <= 256 /\ x4 <= 256 /\ x5 <= 256 /\
                       x6 <= 256 /\ x7 <= 256 /\ x8 <= 256 /\ x9 <= 256 /\ x10 <= 256}


inline_for_extraction noextract
let max56 = pow56 - 1

let qelem_fits1 (x:uint64) (m:scale64) =
  uint_v x <= m * max56


let qelem_fits5 (f:qelem5) (m:scale64_5) =
  let (x1,x2,x3,x4,x5) = f in
  let (m1,m2,m3,m4,m5) = m in
  qelem_fits1 x1 m1 /\
  qelem_fits1 x2 m2 /\
  qelem_fits1 x3 m3 /\
  qelem_fits1 x4 m4 /\
  qelem_fits1 x5 m5


let qelem_wide_fits5 (f:qelem_wide5) (m:scale64_10) =
  let (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) = f in
  let (m1,m2,m3,m4,m5,m6,m7,m8,m9,m10) = m in
  qelem_fits1 x1 m1 /\
  qelem_fits1 x2 m2 /\
  qelem_fits1 x3 m3 /\
  qelem_fits1 x4 m4 /\
  qelem_fits1 x5 m5 /\
  qelem_fits1 x6 m6 /\
  qelem_fits1 x7 m7 /\
  qelem_fits1 x8 m8 /\
  qelem_fits1 x9 m9 /\
  qelem_fits1 x10 m10


noextract
val as_nat5: f:qelem5 -> GTot nat
let as_nat5 f =
  let (s0, s1, s2, s3, s4) = f in
  v s0 + v s1 * pow56 + v s2 * pow112 + v s3 * pow168 + v s4 * pow224


noextract
val wide_as_nat5: f:qelem_wide5 -> GTot nat
let wide_as_nat5 f =
  let (s0, s1, s2, s3, s4, s5, s6, s7, s8, s9) = f in
  v s0 + v s1 * pow56 + v s2 * pow112 + v s3 * pow168 + v s4 * pow224 +
  v s5 * pow280 + v s6 * pow336 + v s7 * pow392 + v s8 * pow448 + v s9 * pow504
