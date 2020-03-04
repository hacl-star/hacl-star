module Hacl.Spec.Poly1305.Field32xN

open Lib.IntTypes
open Lib.IntVector
open Lib.Sequence
open FStar.Mul

open Hacl.Spec.Poly1305.Vec

#reset-options "--z3rlimit 100 --using_facts_from '* -FStar.Seq'"


let scale32 = s:nat{s <= 64}
let scale64 = s:nat{s <= 4096}
let nat5 = (nat & nat & nat & nat & nat)

let scale32_5 = x:nat5{let (x1,x2,x3,x4,x5) = x in
		       x1 <= 64 /\ x2 <= 64 /\ x3 <= 64 /\ x4 <= 64 /\ x5 <= 64}
let scale64_5 = x:nat5{let (x1,x2,x3,x4,x5) = x in
		       x1 <= 4096 /\ x2 <= 4096 /\ x3 <= 4096 /\ x4 <= 4096 /\ x5 <= 4096}

let s64x5 (x:scale64) : scale64_5 = (x,x,x,x,x)

noextract
let ( *^ ) (x:scale32) (y:scale32_5) : scale64_5 =
  assert_norm (64 * 64 = 4096);
  let (y1,y2,y3,y4,y5) = y in
  (x * y1 ,
   x * y2 ,
   x * y3 ,
   x * y4 ,
   x * y5)

noextract
let ( +* ) (x:nat5) (y:nat5) : nat5 =
  let (x1,x2,x3,x4,x5) = x in
  let (y1,y2,y3,y4,y5) = y in
  (x1 + y1 ,
   x2 + y2 ,
   x3 + y3 ,
   x4 + y4 ,
   x5 + y5)

noextract
let ( <=* ) (x:nat5) (y:nat5) : Type =
  let (x1,x2,x3,x4,x5) = x in
  let (y1,y2,y3,y4,y5) = y in
  (x1 <= y1) /\
  (x2 <= y2) /\
  (x3 <= y3) /\
  (x4 <= y4) /\
  (x5 <= y5)

//abstract
let pow26: (pow26: pos { pow2 32 == 64 * pow26 /\ pow2 64 == 4096 * pow26 * pow26 /\ pow26 == pow2 26 }) =
  let pow26: pos = pow2 26 in
  assert_norm (pow2 32 == 64 * pow26);
  assert_norm (pow2 64 == 4096 * pow26 * pow26);
  pow26

let pow52: (pow52:pos {pow52 == pow2 52}) = normalize_term (pow2 52)
let pow78: (pow78:pos {pow78 == pow2 78}) = normalize_term (pow2 78)
let pow104: (pow104:pos {pow104 == pow2 104}) = normalize_term (pow2 104)

inline_for_extraction
let max26 = pow26 - 1


let tup64_5 = (uint64 & uint64 & uint64 & uint64 & uint64)

let tup64_fits1 (f:uint64) (m:scale32) =
  uint_v f <= m * max26

let tup64_wide_fits1 (f:uint64) (m:scale64) =
  uint_v f <= m * max26 * max26

let tup64_fits5 (f:tup64_5) (m:scale32_5) =
  let (x0, x1, x2, x3, x4) = f in
  let (m0, m1, m2, m3, m4) = m in
  tup64_fits1 x0 m0 /\
  tup64_fits1 x1 m1 /\
  tup64_fits1 x2 m2 /\
  tup64_fits1 x3 m3 /\
  tup64_fits1 x4 m4

let tup64_wide_fits5 (f:tup64_5) (m:scale64_5) =
  let (x0, x1, x2, x3, x4) = f in
  let (m0, m1, m2, m3, m4) = m in
  tup64_wide_fits1 x0 m0 /\
  tup64_wide_fits1 x1 m1 /\
  tup64_wide_fits1 x2 m2 /\
  tup64_wide_fits1 x3 m3 /\
  tup64_wide_fits1 x4 m4

noextract
val as_nat5: f:tup64_5 -> nat
let as_nat5  f =
  let (s0, s1, s2, s3, s4) = f in
  v s0 + v s1 * pow26 + v s2 * pow52 + v s3 * pow78 + v s4 * pow104

noextract
let as_pfelem5 (f:tup64_5) : pfelem =
  (as_nat5 f) % prime


let lanes = w:width{w == 1 \/ w == 2 \/ w == 4}
inline_for_extraction
let uint64xN (w:lanes) = vec_t U64 w

inline_for_extraction
let zero (w:lanes) = vec_zero U64 w
inline_for_extraction
let mask26 (w:lanes) = vec_load (u64 0x3ffffff) w
inline_for_extraction
let mask14 (w:lanes) = vec_load (u64 0x3fff) w

inline_for_extraction
let felem5 (w:lanes) = (uint64xN w & uint64xN w & uint64xN w & uint64xN w & uint64xN w)
inline_for_extraction
let felem_wide5 (w:lanes) = felem5 w

let felem_fits1 (#w:lanes) (x:uint64xN w) (m:scale32) =
  forall (i:nat). {:pattern (vec_v x).[i] } i < w ==> uint_v (vec_v x).[i] <= m * max26

let felem_wide_fits1 (#w:lanes) (x:uint64xN w) (m:scale64) =
  forall (i:nat). {:pattern (vec_v x).[i] } i < w ==> uint_v (vec_v x).[i] <= m * max26 * max26

let felem_fits5 (#w:lanes) (f:felem5 w) (m:scale32_5) =
  let (x1,x2,x3,x4,x5) = f in
  let (m1,m2,m3,m4,m5) = m in
  felem_fits1 x1 m1 /\
  felem_fits1 x2 m2 /\
  felem_fits1 x3 m3 /\
  felem_fits1 x4 m4 /\
  felem_fits1 x5 m5

let felem_wide_fits5 (#w:lanes) (f:felem_wide5 w) (m:scale64_5) =
  let (x1,x2,x3,x4,x5) = f in
  let (m1,m2,m3,m4,m5) = m in
  felem_wide_fits1 x1 m1 /\
  felem_wide_fits1 x2 m2 /\
  felem_wide_fits1 x3 m3 /\
  felem_wide_fits1 x4 m4 /\
  felem_wide_fits1 x5 m5

noextract
let transpose (#w:lanes) (f:felem5 w) : lseq tup64_5 w =
  let (f0,f1,f2,f3,f4) = f in
  let v0 = vec_v f0 in
  let v1 = vec_v f1 in
  let v2 = vec_v f2 in
  let v3 = vec_v f3 in
  let v4 = vec_v f4 in
  createi #tup64_5 w (fun i -> (v0.[i],v1.[i],v2.[i],v3.[i],v4.[i]))

noextract
let as_tup64_i (#w:lanes) (f:felem5 w) (i:nat{i < w}): tup64_5 =
  (transpose #w f).[i]

noextract
let feval5 (#w:lanes) (f:felem5 w) : lseq pfelem w =
  map as_pfelem5 (transpose f)

noextract
let fas_nat5 (#w:lanes) (f:felem5 w) : lseq nat w =
  map as_nat5 (transpose f)

noextract
let uint64xN_v (#w:lanes) (e:uint64xN w) : lseq nat w =
  let e = vec_v e in
  createi #nat w (fun i -> uint_v e.[i])

let uint64xN_fits (#w:lanes) (x:uint64xN w) (m:nat) =
  forall (i:nat). i < w ==> uint_v (vec_v x).[i] < m

noextract
let felem_less5 (#w:lanes) (f:felem5 w) (max:nat) : Type0 =
  forall (i:nat). i < w ==> as_nat5 (as_tup64_i f i) < max

noextract
val as_tup5: #w:lanes -> f:lseq (uint64xN w) 5 -> GTot (felem5 w)
let as_tup5 #w s =
  (s.[0], s.[1], s.[2], s.[3], s.[4])

noextract
val lfelem_fits: #w:lanes -> f:lseq (uint64xN w) 5 -> m:scale32_5 -> Type0
let lfelem_fits #w f m =
  felem_fits5 (as_tup5 f) m

noextract
let lfeval (#w:lanes) (f:lseq (uint64xN w) 5) : GTot (lseq pfelem w) =
  feval5 (as_tup5 f)

noextract
let lfelem_less (#w:lanes) (f:lseq (uint64xN w) 5) (max:nat) : Type0 =
  felem_less5 (as_tup5 f) max

inline_for_extraction noextract
val precomp_r5:
    #w:lanes
  -> r:felem5 w
  -> r5:felem5 w
let precomp_r5 #w (r0, r1, r2, r3, r4) =
  [@inline_let]
  let r50 = vec_smul_mod r0 (u64 5) in
  [@inline_let]
  let r51 = vec_smul_mod r1 (u64 5) in
  [@inline_let]
  let r52 = vec_smul_mod r2 (u64 5) in
  [@inline_let]
  let r53 = vec_smul_mod r3 (u64 5) in
  [@inline_let]
  let r54 = vec_smul_mod r4 (u64 5) in
  (r50, r51, r52, r53, r54)

inline_for_extraction noextract
val fadd5:
    #w:lanes
  -> f1:felem5 w
  -> f2:felem5 w
  -> out:felem5 w
let fadd5 #w (f10, f11, f12, f13, f14) (f20, f21, f22, f23, f24) =
  [@inline_let]
  let o0 = f10 +| f20 in
  [@inline_let]
  let o1 = f11 +| f21 in
  [@inline_let]
  let o2 = f12 +| f22 in
  [@inline_let]
  let o3 = f13 +| f23 in
  [@inline_let]
  let o4 = f14 +| f24 in
  (o0, o1, o2, o3, o4)

inline_for_extraction noextract
val smul_felem5:
    #w:lanes
  -> u1:uint64xN w
  -> f2:felem5 w
  -> out:felem_wide5 w
let smul_felem5 #w u1 (f20, f21, f22, f23, f24) =
  [@inline_let]
  let o0 = vec_mul_mod f20 u1 in
  [@inline_let]
  let o1 = vec_mul_mod f21 u1 in
  [@inline_let]
  let o2 = vec_mul_mod f22 u1 in
  [@inline_let]
  let o3 = vec_mul_mod f23 u1 in
  [@inline_let]
  let o4 = vec_mul_mod f24 u1 in
  (o0, o1, o2, o3, o4)

inline_for_extraction noextract
val smul_add_felem5:
    #w:lanes
  -> u1:uint64xN w
  -> f2:felem5 w
  -> acc1:felem_wide5 w
  -> acc2:felem_wide5 w
let smul_add_felem5 #w u1 (f20, f21, f22, f23, f24) (o0, o1, o2, o3, o4) =
  [@inline_let]
  let o0 = vec_add_mod o0 (vec_mul_mod f20 u1) in
  [@inline_let]
  let o1 = vec_add_mod o1 (vec_mul_mod f21 u1) in
  [@inline_let]
  let o2 = vec_add_mod o2 (vec_mul_mod f22 u1) in
  [@inline_let]
  let o3 = vec_add_mod o3 (vec_mul_mod f23 u1) in
  [@inline_let]
  let o4 = vec_add_mod o4 (vec_mul_mod f24 u1) in
  (o0, o1, o2, o3, o4)

inline_for_extraction noextract
val mul_felem5:
    #w:lanes
  -> f1:felem5 w
  -> r:felem5 w
  -> r5:felem5 w
  -> out:felem_wide5 w
let mul_felem5 #w (f10,f11,f12,f13,f14) (r0,r1,r2,r3,r4) (r50,r51,r52,r53,r54) =
  let (a0,a1,a2,a3,a4) = smul_felem5 #w f10 (r0,r1,r2,r3,r4) in
  let (a0,a1,a2,a3,a4) = smul_add_felem5 #w f11 (r54,r0,r1,r2,r3) (a0,a1,a2,a3,a4) in
  let (a0,a1,a2,a3,a4) = smul_add_felem5 #w f12 (r53,r54,r0,r1,r2) (a0,a1,a2,a3,a4) in
  let (a0,a1,a2,a3,a4) = smul_add_felem5 #w f13 (r52,r53,r54,r0,r1) (a0,a1,a2,a3,a4) in
  let (a0,a1,a2,a3,a4) = smul_add_felem5 #w f14 (r51,r52,r53,r54,r0) (a0,a1,a2,a3,a4) in
  (a0,a1,a2,a3,a4)

inline_for_extraction noextract
val carry26:
    #w:lanes
  -> l:uint64xN w
  -> cin:uint64xN w
  -> uint64xN w & uint64xN w
let carry26 #w l cin =
  let l = vec_add_mod l cin in
  (vec_and l (mask26 w), vec_shift_right l 26ul)


inline_for_extraction noextract
val carry_full_felem5:
    #w:lanes
  -> inp:felem5 w
  -> out:felem5 w
let carry_full_felem5 #w (f0, f1, f2, f3, f4) =
  let tmp0,c0 = carry26 f0 (zero w) in
  let tmp1,c1 = carry26 f1 c0 in
  let tmp2,c2 = carry26 f2 c1 in
  let tmp3,c3 = carry26 f3 c2 in
  let tmp4,c4 = carry26 f4 c3 in
  [@inline_let]
  let tmp0' = vec_add_mod tmp0 (vec_smul_mod c4 (u64 5)) in
  (tmp0', tmp1, tmp2, tmp3, tmp4)


inline_for_extraction noextract
val subtract_p5:
    #w:lanes
  -> f:felem5 w
  -> out:felem5 w
let subtract_p5 #w (f0, f1, f2, f3, f4) =
  let mh = vec_load (u64 0x3ffffff) w in
  let ml = vec_load (u64 0x3fffffb) w in
  let mask = vec_eq_mask f4 mh in
  let mask = vec_and mask (vec_eq_mask f3 mh) in
  let mask = vec_and mask (vec_eq_mask f2 mh) in
  let mask = vec_and mask (vec_eq_mask f1 mh) in
  let mask = vec_and mask (vec_gte_mask f0 ml) in
  let ph = vec_and mask mh in
  let pl = vec_and mask ml in
  let o0 = vec_sub_mod f0 pl in
  let o1 = vec_sub_mod f1 ph in
  let o2 = vec_sub_mod f2 ph in
  let o3 = vec_sub_mod f3 ph in
  let o4 = vec_sub_mod f4 ph in
  (o0, o1, o2, o3, o4)

inline_for_extraction noextract
val reduce_felem5:
    #w:lanes
  -> f:felem5 w
  -> out:felem5 w
let reduce_felem5 #w (f0, f1, f2, f3, f4) =
  let (f0, f1, f2, f3, f4) = carry_full_felem5 (f0, f1, f2, f3, f4) in
  let (f0, f1, f2, f3, f4) = carry_full_felem5 (f0, f1, f2, f3, f4) in
  subtract_p5 (f0, f1, f2, f3, f4)

inline_for_extraction noextract
val load_felem5:
    #w:lanes
  -> lo:uint64xN w
  -> hi:uint64xN w
  -> f:felem5 w
let load_felem5 #w lo hi =
  let f0 = vec_and lo (mask26 w) in
  let f1 = vec_and (vec_shift_right lo 26ul) (mask26 w) in
  let f2 = vec_or (vec_shift_right lo 52ul) (vec_shift_left (vec_and hi (mask14 w)) 12ul) in
  let f3 = vec_and (vec_shift_right hi 14ul) (mask26 w) in
  let f4 = vec_shift_right hi 40ul in
  (f0, f1, f2, f3, f4)


inline_for_extraction noextract
val load_felem5_4: lo:uint64xN 4 -> hi:uint64xN 4 -> f:felem5 4
let load_felem5_4 lo hi =
  let mask26 = mask26 4 in
  let m0 = vec_interleave_low_n 2 lo hi in
  let m1 = vec_interleave_high_n 2 lo hi in
  let m2 = cast U64 4 (vec_shift_right (cast U128 2 m0) 48ul) in
  let m3 = cast U64 4 (vec_shift_right (cast U128 2 m1) 48ul) in
  let m4 = vec_interleave_high m0 m1 in
  let t0 = vec_interleave_low m0 m1 in
  let t3 = vec_interleave_low m2 m3 in
  let t2 = vec_shift_right t3 4ul in
  let o2 = vec_and t2 mask26 in
  let t1 = vec_shift_right t0 26ul in
  let o1 = vec_and t1 mask26 in
  let o5 = vec_and t0 mask26 in
  let t3 = vec_shift_right t3 30ul in
  let o3 = vec_and t3 mask26 in
  let o4 = vec_shift_right m4 40ul in
  (o5, o1, o2, o3, o4)

inline_for_extraction noextract
val load_acc5_2:
    f:felem5 2
  -> e:felem5 2
  -> out:felem5 2
let load_acc5_2 (f0, f1, f2, f3, f4) (e0, e1, e2, e3, e4) =
  let f0 = vec_set f0 1ul (u64 0) in
  let f1 = vec_set f1 1ul (u64 0) in
  let f2 = vec_set f2 1ul (u64 0) in
  let f3 = vec_set f3 1ul (u64 0) in
  let f4 = vec_set f4 1ul (u64 0) in
  let (f0, f1, f2, f3, f4) = fadd5 (f0, f1, f2, f3, f4) (e0, e1, e2, e3, e4) in
  (f0, f1, f2, f3, f4)

inline_for_extraction noextract
val load_acc5_4:
    f:felem5 4
  -> e:felem5 4
  -> out:felem5 4
let load_acc5_4 (f0, f1, f2, f3, f4) (e0, e1, e2, e3, e4) =
  let (r0, r1, r2, r3, r4) = (zero 4, zero 4, zero 4, zero 4, zero 4) in
  let r0 = vec_set r0 0ul (vec_get f0 0ul) in
  let r1 = vec_set r1 0ul (vec_get f1 0ul) in
  let r2 = vec_set r2 0ul (vec_get f2 0ul) in
  let r3 = vec_set r3 0ul (vec_get f3 0ul) in
  let r4 = vec_set r4 0ul (vec_get f4 0ul) in
  let (f0, f1, f2, f3, f4) = fadd5 (r0, r1, r2, r3, r4) (e0, e1, e2, e3, e4) in
  (f0, f1, f2, f3, f4)

inline_for_extraction noextract
val store_felem5:
    #w:lanes
  -> f:felem5 w
  -> uint64 & uint64
let store_felem5 #w (f0, f1, f2, f3, f4) =
  let (f0, f1, f2, f3, f4) = (vec_get f0 0ul, vec_get f1 0ul, vec_get f2 0ul, vec_get f3 0ul, vec_get f4 0ul) in
  let lo = (f0 |. (f1 <<. 26ul)) |. (f2 <<. 52ul) in
  let hi = ((f2 >>. 12ul) |. (f3 <<. 14ul)) |. (f4 <<. 40ul) in
  lo, hi

inline_for_extraction noextract
val carry26_wide:
    #w:lanes
  -> l:uint64xN w
  -> cin:uint64xN w
  -> uint64xN w & uint64xN w
let carry26_wide #w l cin = carry26 #w l cin

inline_for_extraction noextract
val carry_wide_felem5:
    #w:lanes
  -> inp:felem_wide5 w
  -> out:felem5 w
let carry_wide_felem5 #w (x0, x1, x2, x3, x4) =
  let mask26 = mask26 w in
  let z0 = vec_shift_right x0 26ul in
  let z1 = vec_shift_right x3 26ul in

  let x0 = vec_and x0 mask26 in
  let x3 = vec_and x3 mask26 in

  let x1 = vec_add_mod x1 z0 in
  let x4 = vec_add_mod x4 z1 in

  let z0 = vec_shift_right x1 26ul in
  let z1 = vec_shift_right x4 26ul in

  let t = vec_shift_left z1 2ul in
  let z1 = vec_add_mod z1 t in
  //let z1 = vec_smul_mod z1 (u64 5) in

  let x1 = vec_and x1 mask26 in
  let x4 = vec_and x4 mask26 in
  let x2 = vec_add_mod x2 z0 in
  let x0 = vec_add_mod x0 z1 in

  let z0 = vec_shift_right x2 26ul in
  let z1 = vec_shift_right x0 26ul in
  let x2 = vec_and x2 mask26 in
  let x0 = vec_and x0 mask26 in
  let x3 = vec_add_mod x3 z0 in
  let x1 = vec_add_mod x1 z1 in

  let z0 = vec_shift_right x3 26ul in
  let x3 = vec_and x3 mask26 in
  let x4 = vec_add_mod x4 z0 in
  (x0, x1, x2, x3, x4)


inline_for_extraction noextract
val fmul_r5:
    #w:lanes
  -> f1:felem5 w
  -> r:felem5 w
  -> r5:felem5 w
  -> out:felem5 w
let fmul_r5 #w (f10, f11, f12, f13, f14) (r0, r1, r2, r3, r4) (r50, r51, r52, r53, r54) =
  let (t0, t1, t2, t3, t4) = mul_felem5 (f10, f11, f12, f13, f14) (r0, r1, r2, r3, r4) (r50, r51, r52, r53, r54) in
  carry_wide_felem5 (t0, t1, t2, t3, t4)

inline_for_extraction noextract
val fadd_mul_r5:
    #w:lanes
  -> acc:felem5 w
  -> f1:felem5 w
  -> r:felem5 w
  -> r5:felem5 w
  -> out:felem5 w
let fadd_mul_r5 #w (a0, a1, a2, a3, a4) (f10, f11, f12, f13, f14) (r0, r1, r2, r3, r4) (r50, r51, r52, r53, r54) =
  let (a0, a1, a2, a3, a4) = fadd5 (a0, a1, a2, a3, a4) (f10, f11, f12, f13, f14) in
  let (t0, t1, t2, t3, t4) = mul_felem5 (a0, a1, a2, a3, a4) (r0, r1, r2, r3, r4) (r50, r51, r52, r53, r54) in
  carry_wide_felem5 (t0, t1, t2, t3, t4)

inline_for_extraction noextract
val fmul_rn5:
    #w:lanes
  -> f1:felem5 w
  -> rn:felem5 w
  -> rn5:felem5 w
  -> out:felem5 w
let fmul_rn5 #w (f10, f11, f12, f13, f14) (rn0, rn1, rn2, rn3, rn4) (rn50, rn51, rn52, rn53, rn54) =
  let (t0, t1, t2, t3, t4) = mul_felem5 (f10, f11, f12, f13, f14) (rn0, rn1, rn2, rn3, rn4) (rn50, rn51, rn52, rn53, rn54) in
  carry_wide_felem5 (t0, t1, t2, t3, t4)

inline_for_extraction noextract
val fmul_r2_normalize5:
    acc:felem5 2
  -> r:felem5 2
  -> r2:felem5 2
  -> out:felem5 2
let fmul_r2_normalize5 (a0, a1, a2, a3, a4) (r0, r1, r2, r3, r4) (r20, r21, r22, r23, r24) =
  let r20 = vec_interleave_low r20 r0 in
  let r21 = vec_interleave_low r21 r1 in
  let r22 = vec_interleave_low r22 r2 in
  let r23 = vec_interleave_low r23 r3 in
  let r24 = vec_interleave_low r24 r4 in

  let (r250, r251, r252, r253, r254) = precomp_r5 #2 (r20, r21, r22, r23, r24) in
  let (o0, o1, o2, o3, o4) = fmul_r5 #2 (a0, a1, a2, a3, a4) (r20, r21, r22, r23, r24) (r250, r251, r252, r253, r254) in

  let o0 = vec_add_mod o0 (vec_interleave_high o0 o0) in
  let o1 = vec_add_mod o1 (vec_interleave_high o1 o1) in
  let o2 = vec_add_mod o2 (vec_interleave_high o2 o2) in
  let o3 = vec_add_mod o3 (vec_interleave_high o3 o3) in
  let o4 = vec_add_mod o4 (vec_interleave_high o4 o4) in
  carry_full_felem5 (o0, o1, o2, o3, o4)

inline_for_extraction
val fmul_r4_normalize5:
    acc:felem5 4
  -> r:felem5 4
  -> r_5:felem5 4
  -> r4:felem5 4
  -> out:felem5 4
let fmul_r4_normalize5 (a0, a1, a2, a3, a4) (r10, r11, r12, r13, r14) (r150, r151, r152, r153, r154) (r40, r41, r42, r43, r44) =
  let (r20, r21, r22, r23, r24) = fmul_r5 (r10, r11, r12, r13, r14) (r10, r11, r12, r13, r14) (r150, r151, r152, r153, r154) in
  let (r30, r31, r32, r33, r34) = fmul_r5 (r20, r21, r22, r23, r24) (r10, r11, r12, r13, r14) (r150, r151, r152, r153, r154) in

  let v12120 = vec_interleave_low r20 r10 in
  let v34340 = vec_interleave_low r40 r30 in
  let r12340 = vec_interleave_low_n 2 v34340 v12120 in

  let v12121 = vec_interleave_low r21 r11 in
  let v34341 = vec_interleave_low r41 r31 in
  let r12341 = vec_interleave_low_n 2 v34341 v12121 in

  let v12122 = vec_interleave_low r22 r12 in
  let v34342 = vec_interleave_low r42 r32 in
  let r12342 = vec_interleave_low_n 2 v34342 v12122 in

  let v12123 = vec_interleave_low r23 r13 in
  let v34343 = vec_interleave_low r43 r33 in
  let r12343 = vec_interleave_low_n 2 v34343 v12123 in

  let v12124 = vec_interleave_low r24 r14 in
  let v34344 = vec_interleave_low r44 r34 in
  let r12344 = vec_interleave_low_n 2 v34344 v12124 in

  let (r123450, r123451, r123452, r123453, r123454) = precomp_r5 #4 (r12340, r12341, r12342, r12343, r12344) in
  let (o0, o1, o2, o3, o4) = fmul_r5 #4 (a0, a1, a2, a3, a4) (r12340, r12341, r12342, r12343, r12344) (r123450, r123451, r123452, r123453, r123454) in

  let v00 = vec_interleave_high_n 2 o0 o0 in
  let v10 = vec_add_mod o0 v00 in
  let v20 = vec_add_mod v10 (vec_permute4 v10 1ul 1ul 1ul 1ul) in

  let v01 = vec_interleave_high_n 2 o1 o1 in
  let v11 = vec_add_mod o1 v01 in
  let v21 = vec_add_mod v11 (vec_permute4 v11 1ul 1ul 1ul 1ul) in

  let v02 = vec_interleave_high_n 2 o2 o2 in
  let v12 = vec_add_mod o2 v02 in
  let v22 = vec_add_mod v12 (vec_permute4 v12 1ul 1ul 1ul 1ul) in

  let v03 = vec_interleave_high_n 2 o3 o3 in
  let v13 = vec_add_mod o3 v03 in
  let v23 = vec_add_mod v13 (vec_permute4 v13 1ul 1ul 1ul 1ul) in

  let v04 = vec_interleave_high_n 2 o4 o4 in
  let v14 = vec_add_mod o4 v04 in
  let v24 = vec_add_mod v14 (vec_permute4 v14 1ul 1ul 1ul 1ul) in
  carry_full_felem5 (v20, v21, v22, v23, v24)

noextract
val set_bit5:
    #w:lanes
  -> f:lseq (uint64xN w) 5
  -> i:size_nat{i <= 128}
  -> out:lseq (uint64xN w) 5
let set_bit5 #w f i =
  let b = u64 1 <<. size (i % 26) in
  let mask = vec_load b w in
  let fi = f.[i / 26] in
  let res = f.[i / 26] <- vec_or fi mask in
  res

inline_for_extraction noextract
val mod_add128:
    a:(uint64 & uint64)
  -> b:(uint64 & uint64)
  -> uint64 & uint64
let mod_add128 (a0, a1) (b0, b1) =
  let r0 = a0 +. b0 in
  let r1 = a1 +. b1 in
  let c = r0 ^. ((r0 ^. b0) |. ((r0 -. b0) ^. b0)) >>. 63ul in
  let r1 = r1 +. c in
  (r0, r1)
