module Hacl.Spec.Curve25519.Field51

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.Sequence
open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST

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

#set-options "--z3rlimit 300"

let ( *^ ) (x:scale64) (y:scale64_5) : scale128_5 =
  let (y1,y2,y3,y4,y5) = y in
  (x * y1 ,
   x * y2 ,
   x * y3 ,
   x * y4 ,
   x * y5)

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

assume val pow51: nat
inline_for_extraction
let max51 = pow51 - 1

assume val lemma_pow_64_51: _:unit{pow2 64 == 8192 * pow51}
assume val lemma_pow_128_51: _:unit{pow2 128 == 67108864 * pow51 * pow51}

// assume val lemma_pow_51_2: _:unit{pow2 102 == pow51 * pow51}
// assume val lemma_pow_51_3: _:unit{pow2 153 == pow51 * pow51 * pow51}
// assume val lemma_pow_51_4: _:unit{pow2 204 == pow51 * pow51 * pow51 * pow51}

let prime = pow2 255 - 19

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

inline_for_extraction
let mask51 = u64 0x7ffffffffffff

inline_for_extraction
val fadd5:
    f1:felem5{felem_fits5 f1 (1, 2, 1, 1, 1)}
  -> f2:felem5{felem_fits5 f2 (1, 2, 1, 1, 1)}
  -> out:felem5{felem_fits5 out (2, 4, 2, 2, 2) /\
      as_nat5 out == as_nat5 f1 + as_nat5 f2}
let fadd5 (f10, f11, f12, f13, f14) (f20, f21, f22, f23, f24) =
  let o0 = f10 +! f20 in
  let o1 = f11 +! f21 in
  let o2 = f12 +! f22 in
  let o3 = f13 +! f23 in
  let o4 = f14 +! f24 in
  (o0, o1, o2, o3, o4)

inline_for_extraction
val fsub5:
    f1:felem5{felem_fits5 f1 (1, 2, 1, 1, 1)}
  -> f2:felem5{felem_fits5 f2 (1, 2, 1, 1, 1)}
  -> out:felem5{felem_fits5 out (9, 10, 9, 9, 9)}
     //as_nat5 out % prime == (as_nat5 f1 - as_nat5 f2) % prime}
let fsub5 (f10, f11, f12, f13, f14) (f20, f21, f22, f23, f24) =
  //assert_norm (0x3fffffffffff68 == pow2 54 - 152);
  //assert_norm (0x3ffffffffffff8 == pow2 54 - 8);
  let o0 = f10 +! u64 0x3fffffffffff68 -! f20 in
  let o1 = f11 +! u64 0x3ffffffffffff8 -! f21 in
  let o2 = f12 +! u64 0x3ffffffffffff8 -! f22 in
  let o3 = f13 +! u64 0x3ffffffffffff8 -! f23 in
  let o4 = f14 +! u64 0x3ffffffffffff8 -! f24 in
  (o0, o1, o2, o3, o4)

inline_for_extraction
val mul_wide64:
    #m1:scale64
  -> #m2:scale64
  -> x:uint64{felem_fits1 x m1}
  -> y:uint64{felem_fits1 y m2 /\ m1 * m2 <= 67108864}
  -> z:uint128{uint_v z == uint_v x * uint_v y /\ felem_wide_fits1 z (m1 * m2)}
let mul_wide64 #m1 #m2 x y =
  mul64_wide x y

#set-options "--z3rlimit 300 --max_fuel 1"

inline_for_extraction
val smul_felem5:
    #m1:scale64
  -> #m2:scale64_5
  -> u1:uint64{felem_fits1 u1 m1}
  -> f2:felem5{felem_fits5 f2 m2 /\ m1 *^ m2 <=* s128x5 67108864}
  -> out:felem_wide5{felem_wide_fits5 out (m1 *^ m2) /\
      wide_as_nat5 out == uint_v u1 * as_nat5 f2}
let smul_felem5 #m1 #m2 u1 (f20, f21, f22, f23, f24) =
  let (m20, m21, m22, m23, m24) = m2 in
  [@inline_let]
  let o0 = mul_wide64 #m1 #m20 u1 f20 in
  [@inline_let]
  let o1 = mul_wide64 #m1 #m21 u1 f21 in
  [@inline_let]
  let o2 = mul_wide64 #m1 #m22 u1 f22 in
  [@inline_let]
  let o3 = mul_wide64 #m1 #m23 u1 f23 in
  [@inline_let]
  let o4 = mul_wide64 #m1 #m24 u1 f24 in
  (o0, o1, o2, o3, o4)

inline_for_extraction
val add_wide128:
    #m1:scale128
  -> #m2:scale128
  -> x:uint128{felem_wide_fits1 x m1}
  -> y:uint128{felem_wide_fits1 y m2 /\ m1 + m2 <= 67108864}
  -> z:uint128{uint_v z == uint_v x + uint_v y /\ felem_wide_fits1 z (m1 + m2)}
let add_wide128 #m1 #m2 x y =
  x +! y

inline_for_extraction
val smul_add_felem5:
    #m1:scale64
  -> #m2:scale64_5
  -> #m3:scale128_5
  -> u1:uint64{felem_fits1 u1 m1}
  -> f2:felem5{felem_fits5 f2 m2}
  -> acc1:felem_wide5{felem_wide_fits5 acc1 m3 /\ m3 +* m1 *^ m2 <=* s128x5 67108864}
  -> acc2:felem_wide5{
      wide_as_nat5 acc2 == wide_as_nat5 acc1 + uint_v u1 * as_nat5 f2 /\
      felem_wide_fits5 acc2 (m3 +* m1 *^ m2)}
let smul_add_felem5 #m1 #m2 #m3 u1 (f20, f21, f22, f23, f24) (o0, o1, o2, o3, o4) =
  let (m20, m21, m22, m23, m24) = m2 in
  let (m30, m31, m32, m33, m34) = m3 in
  [@inline_let]
  let o0 = o0 +! mul_wide64 #m1 #m20 u1 f20 in
  [@inline_let]
  let o1 = o1 +! mul_wide64 #m1 #m21 u1 f21 in
  [@inline_let]
  let o2 = o2 +! mul_wide64 #m1 #m22 u1 f22 in
  [@inline_let]
  let o3 = o3 +! mul_wide64 #m1 #m23 u1 f23 in
  [@inline_let]
  let o4 = o4 +! mul_wide64 #m1 #m24 u1 f24 in
  (o0, o1, o2, o3, o4)

inline_for_extraction
val mul_felem5:
    f1:felem5{felem_fits5 f1 (9, 10, 9, 9, 9)}
  -> r:felem5{felem_fits5 r (9, 10, 9, 9, 9)}
  -> r19:felem5{felem_fits5 r19 (171, 190, 171, 171, 171)}
  -> out:felem_wide5{felem_wide_fits5 out (6579, 4797, 3340, 1881, 423)}
    //wide_as_nat5 out % prime == (as_nat5 f1 * as_nat5 r) % prime
let mul_felem5 (f10, f11, f12, f13, f14) (r0, r1, r2, r3, r4) (r190, r191, r192, r193, r194) =
  let (o0, o1, o2, o3, o4) = smul_felem5 #9 #(9, 10, 9, 9, 9) f10 (r0, r1, r2, r3, r4) in
  let (o0, o1, o2, o3, o4) = smul_add_felem5 #10 #(171, 9, 10, 9, 9) #(81, 90, 81, 81, 81) f11 (r194, r0, r1, r2, r3) (o0, o1, o2, o3, o4) in
  let (o0, o1, o2, o3, o4) = smul_add_felem5 #9 #(171, 171, 9, 10, 9) #(1791, 180, 181, 171, 171)  f12 (r193, r194, r0, r1, r2) (o0, o1, o2, o3, o4) in
  let (o0, o1, o2, o3, o4) = smul_add_felem5 #9 #(171, 171, 171, 9, 10) #(3330, 1719, 262, 261, 252) f13 (r192, r193, r194, r0, r1) (o0, o1, o2, o3, o4) in
  let (o0, o1, o2, o3, o4) = smul_add_felem5 #9 #(190, 171, 171, 171, 9) #(4869, 3258, 1801, 342, 342) f14 (r191, r192, r193, r194, r0) (o0, o1, o2, o3, o4) in
  (o0, o1, o2, o3, o4)

inline_for_extraction
val carry51:
    l:uint64
  -> cin:uint64
  -> Pure (uint64 & uint64)
    (requires uint_v l + uint_v cin < pow2 64)
    (ensures fun (l0, l1) -> felem_fits1 l0 1 /\ uint_v l1 < pow2 13)
let carry51 l cin =
  let l = l +! cin in
  admit();
  (l &. mask51, l >>. 51ul)

inline_for_extraction
val carry51_wide:
    #m:scale64{m < 8192}
  -> l:uint128{felem_wide_fits1 l m}
  -> cin:uint64
  -> Pure (uint64 & uint64)
    (requires True)
    (ensures fun (l0, l1) -> felem_fits1 l0 1 /\ felem_fits1 l1 (m + 1)) //or m
let carry51_wide #m l cin =
  let l = l +! to_u128 cin in
  [@inline_let]
  let l0 = to_u64 l &. mask51 in
  [@inline_let]
  let l1 = to_u64 (l >>. 51ul) in
  admit();
  (l0, l1)

#set-options "--max_fuel 1"

inline_for_extraction
val carry_wide5:
    inp:felem_wide5{felem_wide_fits5 inp (6579, 4797, 3340, 1881, 423)}
  -> out:felem5{felem_fits5 out (1, 2, 1, 1, 1)}
let carry_wide5 (i0, i1, i2, i3, i4) =
  assert_norm (6579 < pow2 13);
  assert_norm (pow2 13 < max51);
  let tmp0, c = carry51_wide #6579 i0 (u64 0) in
  let tmp1, c = carry51_wide #4797 i1 c in
  let tmp2, c = carry51_wide #3340 i2 c in
  let tmp3, c = carry51_wide #1881 i3 c in
  let tmp4, c = carry51_wide #423 i4 c in

  let tmp0, c = carry51 tmp0 (c *! u64 19) in
  [@inline_let]
  let tmp1 = tmp1 +! c in
  (tmp0, tmp1, tmp2, tmp3, tmp4)

// inline_for_extraction
// val carry_felem5: felem5 -> felem5
// let carry_felem5 (f0, f1, f2, f3, f4) =
//   let tmp0, c = carry51 f0 (u64 0) in
//   let tmp1, c = carry51 f1 c in
//   let tmp2, c = carry51 f2 c in
//   let tmp3, c = carry51 f3 c in
//   let tmp4, c = carry51 f4 c in
//   let tmp0, c = carry51 tmp0 (c *. u64 19) in
//   let tmp1 = tmp1 +. c in
//   (tmp0, tmp1, tmp2, tmp3, tmp4)

inline_for_extraction
val precomp_r19:
    f2:felem5{felem_fits5 f2 (9, 10, 9, 9, 9)}
  -> r19:felem5{felem_fits5 r19 (171, 190, 171, 171, 171)}
let precomp_r19 (f20, f21, f22, f23, f24) =
  [@inline_let]
  let r190 = f20 *! u64 19 in
  [@inline_let]
  let r191 = f21 *! u64 19 in
  [@inline_let]
  let r192 = f22 *! u64 19 in
  [@inline_let]
  let r193 = f23 *! u64 19 in
  [@inline_let]
  let r194 = f24 *! u64 19 in
  (r190, r191, r192, r193, r194)

inline_for_extraction
val fmul5:
    f1:felem5{felem_fits5 f1 (9, 10, 9, 9, 9)}
  -> f2:felem5{felem_fits5 f2 (9, 10, 9, 9, 9)}
  -> out:felem5{felem_fits5 out (1, 2, 1, 1, 1)}
let fmul5 (f10, f11, f12, f13, f14) (f20, f21, f22, f23, f24) =
  let (tmp0, tmp1, tmp2, tmp3, tmp4) = precomp_r19 (f20, f21, f22, f23, f24) in
  let (tmp_w0, tmp_w1, tmp_w2, tmp_w3, tmp_w4) = mul_felem5 (f10, f11, f12, f13, f14) (f20, f21, f22, f23, f24) (tmp0, tmp1, tmp2, tmp3, tmp4) in
  carry_wide5 (tmp_w0, tmp_w1, tmp_w2, tmp_w3, tmp_w4)

inline_for_extraction
val fmul15:
    f1:felem5{felem_fits5 f1 (9, 10, 9, 9, 9)}
  -> f2:uint64{felem_fits1 f2 1}
  -> out:felem5{felem_fits5 out (1, 2, 1, 1, 1)}
let fmul15 f1 f2 =
  let tmp_w = smul_felem5 #1 #(9, 10, 9, 9, 9) f2 f1 in
  carry_wide5 tmp_w

inline_for_extraction
val fsqr5:
    f:felem5{felem_fits5 f (9, 10, 9, 9, 9)}
  -> out:felem5{felem_fits5 out (1, 2, 1, 1, 1)}
let fsqr5 f =
  let (f0, f1, f2, f3, f4) = f in
  let d0 = u64 2 *. f0 in
  let d1 = u64 2 *. f1 in
  let d2 = u64 38 *. f2 in
  let d3 = u64 19 *. f3 in
  let d419 = u64 19 *. f4 in
  let d4 = u64 2 *. d419 in
  let s0 = mul64_wide f0 f0 +. mul64_wide d4 f1 +. mul64_wide d2 f3 in
  let s1 = mul64_wide d0 f1 +. mul64_wide d4 f2 +. mul64_wide d3 f3 in
  let s2 = mul64_wide d0 f2 +. mul64_wide f1 f1 +. mul64_wide d4 f3 in
  let s3 = mul64_wide d0 f3 +. mul64_wide d1 f2 +. mul64_wide f4 d419 in
  let s4 = mul64_wide d0 f4 +. mul64_wide d1 f3 +. mul64_wide f2 f2 in
  admit();
  carry_wide5 (s0, s1, s2, s3, s4)


val point_add_and_double_5:
    x1:felem5{felem_fits5 x1 (1, 2, 1, 1, 1)}
  -> z1:felem5{felem_fits5 z1 (1, 2, 1, 1, 1)}
  -> x2:felem5{felem_fits5 x2 (1, 2, 1, 1, 1)}
  -> z2:felem5{felem_fits5 z2 (1, 2, 1, 1, 1)}
  -> x3:felem5{felem_fits5 x3 (1, 2, 1, 1, 1)}
  -> z3:felem5{felem_fits5 z3 (1, 2, 1, 1, 1)}
  -> Pure (tuple4 felem5 felem5 felem5 felem5)
    (requires True)
    (ensures fun res ->
      let (x2, z2, x3, z3) = res in
      felem_fits5 x2 (1, 2, 1, 1, 1) /\
      felem_fits5 z2 (1, 2, 1, 1, 1) /\
      felem_fits5 x3 (1, 2, 1, 1, 1) /\
      felem_fits5 z3 (1, 2, 1, 1, 1))
let point_add_and_double_5 x1 z1 x2 z2 x3 z3 =
  let a = fadd5 x2 z2 in
  let b = fsub5 x2 z2 in
  let c = fadd5 x3 z3 in
  let d = fsub5 x3 z3 in
  let d = fmul5 d a in
  let c = fmul5 c b in
  let x3 = fadd5 d c in
  let x3 = fsqr5 x3 in
  let z3 = fsub5 d c in
  let z3 = fsqr5 z3 in
  let z3 = fmul5 z3 x1 in
  let c = fsqr5 a in
  let d = fsqr5 b in
  let x2 = fmul5 c d in
  let b = fsub5 c d in
  let a = fmul15 b (u64 121665) in
  let a = fadd5 a c in
  let z2 = fmul5 b a in
  (x2, z2, x3, z3)
