module Hacl.Spec.Poly

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

module S = Spec.Poly

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

inline_for_extraction
let felem5 = (uint64 & uint64 & uint64 & uint64 & uint64)
inline_for_extraction
let felem_wide5 = felem5

(* Evaluation function *)
let pow26: (pow26: pos{pow2 32 == 64 * pow26 /\ pow2 64 == 4096 * pow26 * pow26 /\ pow26 == pow2 26}) =
  let pow26: pos = pow2 26 in
  assert_norm (pow2 32 == 64 * pow26);
  assert_norm (pow2 64 == 4096 * pow26 * pow26);
  pow26

let pow52: (pow52:pos{pow52 == pow2 52}) = normalize_term (pow2 52)
let pow78: (pow78:pos{pow78 == pow2 78}) = normalize_term (pow2 78)
let pow104: (pow104:pos{pow104 == pow2 104}) = normalize_term (pow2 104)

let as_nat5 (f:felem5) : nat =
  let (s0, s1, s2, s3, s4) = f in
  v s0 + v s1 * pow26 + v s2 * pow52 + v s3 * pow78 + v s4 * pow104

let feval5 (f:felem5) : S.felem =
  as_nat5 f % S.prime

let to_felem5 (l:lseq uint64 5) : felem5 =
  (l.[0], l.[1], l.[2], l.[3], l.[4])


(* The following reasoning allows to avoid an integer overflow
by tracking a number of bits used in the "extra" space *)
let scale32 = s:nat{s <= 64}
let scale64 = s:nat{s <= 4096}
let nat5 = (nat & nat & nat & nat & nat)

let scale32_5 = x:nat5{let (x1,x2,x3,x4,x5) = x in
		       x1 <= 64 /\ x2 <= 64 /\ x3 <= 64 /\ x4 <= 64 /\ x5 <= 64}
let scale64_5 = x:nat5{let (x1,x2,x3,x4,x5) = x in
		       x1 <= 4096 /\ x2 <= 4096 /\ x3 <= 4096 /\ x4 <= 4096 /\ x5 <= 4096}

let s64x5 (x:scale64) : scale64_5 = (x,x,x,x,x)

let ( *^ ) (x:scale32) (y:scale32_5) : scale64_5 =
  assert_norm (64 * 64 = 4096);
  let (y1,y2,y3,y4,y5) = y in
  (x * y1,
   x * y2,
   x * y3,
   x * y4,
   x * y5)

let ( +* ) (x:nat5) (y:nat5) : nat5 =
  let (x1,x2,x3,x4,x5) = x in
  let (y1,y2,y3,y4,y5) = y in
  (x1 + y1,
   x2 + y2,
   x3 + y3,
   x4 + y4,
   x5 + y5)

let ( <=* ) (x:nat5) (y:nat5) : Type =
  let (x1,x2,x3,x4,x5) = x in
  let (y1,y2,y3,y4,y5) = y in
  (x1 <= y1) /\
  (x2 <= y2) /\
  (x3 <= y3) /\
  (x4 <= y4) /\
  (x5 <= y5)


let max26 = pow26 - 1

let felem_fits1 (x:uint64) (m:scale32) =
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

(* Low-level specification of bignum operations over the Poly1305 finite field *)

inline_for_extraction
let mask26 = u64 0x3ffffff
inline_for_extraction
let mask14 = u64 0x3fff


inline_for_extraction
val precomp_r5: r:felem5{felem_fits5 r (1,1,1,1,1)} -> res:felem5{felem_fits5 res (5,5,5,5,5)}
let precomp_r5 (r0, r1, r2, r3, r4) =
  let r50 = u64 5 *! r0 in
  let r51 = u64 5 *! r1 in
  let r52 = u64 5 *! r2 in
  let r53 = u64 5 *! r3 in
  let r54 = u64 5 *! r4 in
  (r50, r51, r52, r53, r54)


inline_for_extraction
val add5: f1:felem5 -> f2:felem5 -> felem5
let add5 (f10, f11, f12, f13, f14) (f20, f21, f22, f23, f24) =
  let o0 = f10 +. f20 in
  let o1 = f11 +. f21 in
  let o2 = f12 +. f22 in
  let o3 = f13 +. f23 in
  let o4 = f14 +. f24 in
  (o0, o1, o2, o3, o4)


inline_for_extraction
val smul5: u1:uint64 -> f2:felem5 -> felem_wide5
let smul5 u1 (f20, f21, f22, f23, f24) =
  let o0 = u1 *. f20 in
  let o1 = u1 *. f21 in
  let o2 = u1 *. f22 in
  let o3 = u1 *. f23 in
  let o4 = u1 *. f24 in
  (o0, o1, o2, o3, o4)


inline_for_extraction
val smul_add5: u1:uint64 -> f2:felem5 -> acc1:felem_wide5 -> felem_wide5
let smul_add5 u1 (f20, f21, f22, f23, f24) (o0, o1, o2, o3, o4) =
  let o0 = o0 +. u1 *. f20 in
  let o1 = o1 +. u1 *. f21 in
  let o2 = o2 +. u1 *. f22 in
  let o3 = o3 +. u1 *. f23 in
  let o4 = o4 +. u1 *. f24 in
  (o0, o1, o2, o3, o4)


inline_for_extraction
val mul5: f1:felem5 -> r:felem5 -> r5:felem5 -> felem_wide5
let mul5 (f10,f11,f12,f13,f14) (r0,r1,r2,r3,r4) (r50,r51,r52,r53,r54) =
  let (a0,a1,a2,a3,a4) = smul5 f10 (r0,r1,r2,r3,r4) in
  let (a0,a1,a2,a3,a4) = smul_add5 f11 (r54,r0,r1,r2,r3) (a0,a1,a2,a3,a4) in
  let (a0,a1,a2,a3,a4) = smul_add5 f12 (r53,r54,r0,r1,r2) (a0,a1,a2,a3,a4) in
  let (a0,a1,a2,a3,a4) = smul_add5 f13 (r52,r53,r54,r0,r1) (a0,a1,a2,a3,a4) in
  let (a0,a1,a2,a3,a4) = smul_add5 f14 (r51,r52,r53,r54,r0) (a0,a1,a2,a3,a4) in
  (a0,a1,a2,a3,a4)


inline_for_extraction
val carry26: l:uint64 -> cin:uint64 -> uint64 & uint64
let carry26 l cin =
  let l = l +. cin in
  l &. mask26,  l >>. 26ul

inline_for_extraction
val carry26_wide: l:uint64 -> cin:uint64 -> uint64 & uint64
let carry26_wide l cin = carry26 l cin


inline_for_extraction
val carry_wide_felem5: inp:felem_wide5 -> felem5
let carry_wide_felem5 (i0, i1, i2, i3, i4) =
  let t0,c0 = carry26_wide i0 (u64 0) in
  let t1,c1 = carry26_wide i1 c0 in
  let t2,c2 = carry26_wide i2 c1 in
  let t3,c3 = carry26_wide i3 c2 in
  let t4,c4 = carry26_wide i4 c3 in
  let t0,c5 = carry26 t0 (c4 *. u64 5) in
  let t1 = t1 +. c5 in
  (t0, t1, t2, t3, t4)


inline_for_extraction
val add_mul_r5: acc:felem5 -> f1:felem5 -> r:felem5 -> r5:felem5 -> felem5
let add_mul_r5 (a0, a1, a2, a3, a4) (f10, f11, f12, f13, f14) (r0, r1, r2, r3, r4) (r50, r51, r52, r53, r54) =
  let (a0, a1, a2, a3, a4) = add5 (a0, a1, a2, a3, a4) (f10, f11, f12, f13, f14) in
  let (t0, t1, t2, t3, t4) = mul5 (a0, a1, a2, a3, a4) (r0, r1, r2, r3, r4) (r50, r51, r52, r53, r54) in
  carry_wide_felem5 (t0, t1, t2, t3, t4)


inline_for_extraction
val load_felem5: lo:uint64 -> hi:uint64 -> felem5
let load_felem5 lo hi =
  let f0 = lo &. mask26 in
  let f1 = (lo >>. 26ul) &. mask26 in
  let f2 = (lo >>. 52ul) |. ((hi &. mask14) <<. 12ul) in
  let f3 = (hi >>. 14ul) &. mask26 in
  let f4 = hi >>. 40ul in
  (f0, f1, f2, f3, f4)


inline_for_extraction
val set_bit128_5: f:felem5 -> felem5
let set_bit128_5 (f0, f1, f2, f3, f4) =
  let f4' = f4 |. u64 0x1000000 in
  (f0, f1, f2, f3, f4')
