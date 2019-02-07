module Hacl.Spec.Curve25519.Field51.Definition

open Lib.Sequence
open Lib.IntTypes
open NatPrime

#reset-options "--z3rlimit 20"

let felem5 = (uint64 * uint64 * uint64 * uint64 * uint64)
let felem_wide5 = (uint128 * uint128 * uint128 * uint128 * uint128)

let scale64 = s:nat{s <= 8192}
let scale128 = s:nat{s <= 67108864}
let nat5 = (nat * nat * nat * nat * nat)

let scale64_5 = x:nat5{let (x1,x2,x3,x4,x5) = x in
		       x1 <= 8192 /\ x2 <= 8192 /\ x3 <= 8192 /\ x4 <= 8192 /\ x5 <= 8192}
let scale128_5 = x:nat5{let (x1,x2,x3,x4,x5) = x in
 		        x1 <= 67108864 /\ x2 <= 67108864 /\ x3 <= 67108864 /\ x4 <= 67108864 /\ x5 <= 67108864}

let s64x5 (x:scale64) : scale64_5 = (x,x,x,x,x)
let s128x5 (x:scale128) : scale128_5 = (x,x,x,x,x)

open FStar.Mul

let ( <=* ) (x:nat5) (y:nat5) : Type =
  let (x1,x2,x3,x4,x5) = x in
  let (y1,y2,y3,y4,y5) = y in
  (x1 <= y1) /\
  (x2 <= y2) /\
  (x3 <= y3) /\
  (x4 <= y4) /\
  (x5 <= y5)

let ( +* ) (x:nat5) (y:nat5) : nat5 =
  let (x1,x2,x3,x4,x5) = x in
  let (y1,y2,y3,y4,y5) = y in
  (x1 + y1 ,
   x2 + y2 ,
   x3 + y3 ,
   x4 + y4 ,
   x5 + y5)

let ( ** ) (x:nat5) (y:nat5) : nat5 =
  let (x1,x2,x3,x4,x5) = x in
  let (y1,y2,y3,y4,y5) = y in
  (x1 * y1 ,
   x2 * y2 ,
   x3 * y3 ,
   x4 * y4 ,
   x5 * y5)

#set-options "--z3rlimit 100"

let ( *^ ) (x:scale64) (y:scale64_5) : scale128_5 =
  assert_norm (8192 * 8192 = 67108864);
  let (y1,y2,y3,y4,y5) = y in
  (x * y1 ,
   x * y2 ,
   x * y3 ,
   x * y4 ,
   x * y5)

#reset-options "--z3rlimit 50  --using_facts_from '* -FStar.Seq'"

assume val pow51: nat
inline_for_extraction
let max51 = pow51 - 1

inline_for_extraction
let mask51 : x:uint64{v x == pow2 51 - 1} =
  assert_norm (pow2 51 - 1 == 0x7ffffffffffff);
  u64 0x7ffffffffffff

assume val lemma_pow_64_51: _:unit{pow2 64 == 8192 * pow51}
assume val lemma_pow_128_51: _:unit{pow2 128 == 67108864 * pow51 * pow51}

// assume val lemma_pow_51_2: _:unit{pow2 102 == pow51 * pow51}
// assume val lemma_pow_51_3: _:unit{pow2 153 == pow51 * pow51 * pow51}
// assume val lemma_pow_51_4: _:unit{pow2 204 == pow51 * pow51 * pow51 * pow51}

let felem_fits1 (x:uint64) (m:scale64) =
  uint_v x <= m * max51

let felem_wide_fits1 (x:uint128) (m:scale128) =
  uint_v x <= m * max51 * max51

let felem_fits5 (f:felem5) (m:scale64_5) =
  let (x1,x2,x3,x4,x5) = f in
  let (m1,m2,m3,m4,m5) = m in
  felem_fits1 x1 m1 /\
  felem_fits1 x2 m2 /\
  felem_fits1 x3 m3 /\
  felem_fits1 x4 m4 /\
  felem_fits1 x5 m5

let felem_wide_fits5 (f:felem_wide5) (m:scale128_5) =
  let (x1,x2,x3,x4,x5) = f in
  let (m1,m2,m3,m4,m5) = m in
  felem_wide_fits1 x1 m1 /\
  felem_wide_fits1 x2 m2 /\
  felem_wide_fits1 x3 m3 /\
  felem_wide_fits1 x4 m4 /\
  felem_wide_fits1 x5 m5

noextract
val as_nat5: f:felem5 -> GTot nat
let as_nat5 f =
  let (s0, s1, s2, s3, s4) = f in
  uint_v s0 + (uint_v s1 * pow51) + (uint_v s2 * pow51 * pow51) +
    (uint_v s3 * pow51 * pow51 * pow51) + (uint_v s4 * pow51 * pow51 * pow51 * pow51)

noextract
val wide_as_nat5: f:felem_wide5 -> GTot nat
let wide_as_nat5 f =
  let (s0, s1, s2, s3, s4) = f in
  uint_v s0 + (uint_v s1 * pow51) + (uint_v s2 * pow51 * pow51) +
    (uint_v s3 * pow51 * pow51 * pow51) + (uint_v s4 * pow51 * pow51 * pow51 * pow51)

let feval (f:felem5) : GTot felem = (as_nat5 f) % prime
let feval_wide (f:felem_wide5) : GTot felem = (wide_as_nat5 f) % prime
