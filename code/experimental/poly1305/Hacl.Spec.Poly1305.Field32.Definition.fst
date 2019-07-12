module Hacl.Spec.Poly1305.Field32.Definition

open Lib.Sequence
open Lib.IntTypes
open NatPrime

#reset-options "--z3rlimit 50  --using_facts_from '* -FStar.Seq'"

let felem5 = (uint32 * uint32 * uint32 * uint32 * uint32)
let felem_wide5 = (uint64 * uint64 * uint64 * uint64 * uint64)

let scale32 = s:nat{s <= 64}
let scale64 = s:nat{s <= 4096}
let nat5 = (nat * nat * nat * nat * nat)

let scale32_5 = x:nat5{let (x1,x2,x3,x4,x5) = x in
		       x1 <= 64 /\ x2 <= 64 /\ x3 <= 64 /\ x4 <= 64 /\ x5 <= 64}
let scale64_5 = x:nat5{let (x1,x2,x3,x4,x5) = x in
		       x1 <= 4096 /\ x2 <= 4096 /\ x3 <= 4096 /\ x4 <= 4096 /\ x5 <= 4096}

let s32x5 (x:scale32) : scale32_5 = (x,x,x,x,x)
let s64x5 (x:scale64) : scale64_5 = (x,x,x,x,x)

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

let ( *^ ) (x:scale32) (y:scale32_5) : scale64_5 =
  assert_norm (64 * 64 = 4096);
  let (y1,y2,y3,y4,y5) = y in
  (x * y1 ,
   x * y2 ,
   x * y3 ,
   x * y4 ,
   x * y5)

assume val pow26: nat
inline_for_extraction
let max26 = pow26 - 1

inline_for_extraction
let mask26: x:uint32{v x == pow2 26 - 1} =
  assert_norm (pow2 26 - 1 == 0x3ffffff);
  u32 0x3ffffff

assume val lemma_pow_32_26: _:unit{pow2 32 == 64 * pow26}
assume val lemma_pow_64_26: _:unit{pow2 64 == 4096 * pow26 * pow26}

//let _ : (x:unit{pow2 32 == 64 * pow2 26}) =
//      assert_norm (pow2 32 == 64 * pow2 26)
//let _ : (x:unit{pow2 64 == 4096 * pow2 26 * pow2 26}) =
//      assert_norm (pow2 64 == 4096 * pow2 26 * pow2 26)


let felem_fits1 (x:uint32) (m:scale32) =
  uint_v x <= m * max26

let felem_wide_fits1 (x:uint64) (m:scale64) =
  uint_v x <= m * max26 * max26

let felem_fits5 (f:felem5) (m:scale32_5) =
  let (x1,x2,x3,x4,x5) = f in
  let (m1,m2,m3,m4,m5) = m in
  felem_fits1 x1 m1 /\
  felem_fits1 x2 m2 /\
  felem_fits1 x3 m3 /\
  felem_fits1 x4 m4 /\
  felem_fits1 x5 m5

let felem_wide_fits5 (f:felem_wide5) (m:scale64_5) =
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
  let (s0,s1,s2,s3,s4) = f in
  uint_v s0 + (uint_v s1 * pow26) + (uint_v s2 * pow26 * pow26) +
    (uint_v s3 * pow26 * pow26 * pow26) + (uint_v s4 * pow26 * pow26 * pow26 * pow26)

noextract
val wide_as_nat5: f:felem_wide5 -> GTot nat
let wide_as_nat5 f =
  let (s0,s1,s2,s3,s4) = f in
  uint_v s0 + (uint_v s1 * pow26) + (uint_v s2 * pow26 * pow26) +
    (uint_v s3 * pow26 * pow26 * pow26) + (uint_v s4 * pow26 * pow26 * pow26 * pow26)

let feval (f:felem5) : GTot felem = (as_nat5 f) % prime
let feval_wide (f:felem_wide5) : GTot felem = (wide_as_nat5 f) % prime
