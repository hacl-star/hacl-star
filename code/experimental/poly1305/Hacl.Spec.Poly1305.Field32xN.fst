module Hacl.Spec.Poly1305.Field32xN

open Lib.IntTypes
open Lib.IntVector
open Lib.Sequence

(* high-level spec *)
let prime:pos =
  assert_norm (pow2 130 - 5 > 0);
  pow2 130 - 5

let pfelem = x:nat{x < prime}
let pfadd (f1:pfelem) (f2:pfelem) : pfelem = (f1 + f2) % prime
let pfmul (f1:pfelem) (f2:pfelem) : pfelem = (f1 `op_Multiply` f2) % prime

(* low-level spec *)
let scale32 = s:nat{s <= 64}
let scale64 = s:nat{s <= 4096}
let nat5 = (nat * nat * nat * nat * nat)

let scale32_5 = x:nat5{let (x1,x2,x3,x4,x5) = x in
		       x1 <= 64 /\ x2 <= 64 /\ x3 <= 64 /\ x4 <= 64 /\ x5 <= 64}
let scale64_5 = x:nat5{let (x1,x2,x3,x4,x5) = x in
		       x1 <= 4096 /\ x2 <= 4096 /\ x3 <= 4096 /\ x4 <= 4096 /\ x5 <= 4096}

let s64x5 (x:scale64) : scale64_5 = (x,x,x,x,x)

open FStar.Mul

#reset-options "--z3rlimit 100 --using_facts_from '* -FStar.Seq'"

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

assume val pow26: nat
inline_for_extraction
let max26 = pow26 - 1

assume val lemma_pow_32_26: _:unit{pow2 32 == 64 * pow26}
assume val lemma_pow_64_26: _:unit{pow2 64 == 4096 * pow26 * pow26}


let tup64_5 = (uint64 & uint64 & uint64 & uint64 & uint64)

let tup64_fits1 (f:uint64) (m:scale32) =
  uint_v f <= m * max26

let tup64_fits5 (f:tup64_5) (m:scale32_5) =
  let (x0, x1, x2, x3, x4) = f in
  let (m0, m1, m2, m3, m4) = m in
  tup64_fits1 x0 m0 /\
  tup64_fits1 x1 m1 /\
  tup64_fits1 x2 m2 /\
  tup64_fits1 x3 m3 /\
  tup64_fits1 x4 m4

noextract
val as_nat5: f:tup64_5 -> nat
let as_nat5  f =
  let (s0,s1,s2,s3,s4) = f in
  uint_v s0 + (uint_v s1 * pow26) + (uint_v s2 * pow26 * pow26) +
    (uint_v s3 * pow26 * pow26 * pow26) + (uint_v s4 * pow26 * pow26 * pow26 * pow26)

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
  forall (i:nat). i < w ==> uint_v (vec_v x).[i] <= m * max26

let felem_wide_fits1 (#w:lanes) (x:uint64xN w) (m:scale64) =
  forall (i:nat). i < w ==> uint_v (vec_v x).[i] <= m * max26 * max26

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
let as_tup64_i (#w:lanes) (f:felem5 w) (i:nat{i < w}): tup64_5 =
  let (f0,f1,f2,f3,f4) = f in
  let v0 = vec_v f0 in
  let v1 = vec_v f1 in
  let v2 = vec_v f2 in
  let v3 = vec_v f3 in
  let v4 = vec_v f4 in
  (v0.[i],v1.[i],v2.[i],v3.[i],v4.[i])

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
let acc_inv_t (#w:lanes) (acc:felem5 w) : Type0 =
  let (o0, o1, o2, o3, o4) = acc in
  forall (i:nat). i < w ==>
   (if uint_v (vec_v o1).[i] >= pow2 26 then
      tup64_fits5 (as_tup64_i acc i) (1, 2, 1, 1, 1) /\
      uint_v (vec_v o1).[i] % pow2 26 < 64
    else tup64_fits5 (as_tup64_i acc i) (1, 1, 1, 1, 1))

noextract
val precomp_r5:
    #w:lanes
  -> r:felem5 w
  -> r5:felem5 w
let precomp_r5 #w (r0, r1, r2, r3, r4) =
  let r50 = vec_smul_mod r0 (u64 5) in
  let r51 = vec_smul_mod r1 (u64 5) in
  let r52 = vec_smul_mod r2 (u64 5) in
  let r53 = vec_smul_mod r3 (u64 5) in
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
let carry_wide_felem5 #w (i0, i1, i2, i3, i4) =
  let tmp0,c0 = carry26_wide i0 (zero w) in
  let tmp1,c1 = carry26_wide i1 c0 in
  let tmp2,c2 = carry26_wide i2 c1 in
  let tmp3,c3 = carry26_wide i3 c2 in
  let tmp4,c4 = carry26_wide i4 c3 in
  let tmp0,c5 = carry26 tmp0 (vec_smul_mod c4 (u64 5)) in
  let tmp1 = vec_add_mod tmp1 c5 in
  (tmp0, tmp1, tmp2, tmp3, tmp4)

inline_for_extraction noextract
val fmul_r5:
    #w:lanes
  -> f1:felem5 w
  -> r:felem5 w
  -> r5:felem5 w
  -> out:felem5 w
let fmul_r5 #w (f10, f11, f12, f13, f14) (r0, r1, r2, r3, r4) (r50, r51, r52, r53, r54) =
  let (t0, t1, t2, t3, t4) =
    mul_felem5 (f10, f11, f12, f13, f14) (r0, r1, r2, r3, r4) (r50, r51, r52, r53, r54) in
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
  let (t0, t1, t2, t3, t4) = mul_felem5 (f10, f11, f12, f13, f14)
    (rn0, rn1, rn2, rn3, rn4) (rn50, rn51, rn52, rn53, rn54) in
  carry_wide_felem5 (t0, t1, t2, t3, t4)
