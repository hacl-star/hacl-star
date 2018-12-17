module Hacl.Spec.Poly1305.Field32

open Lib.Sequence
open Lib.IntTypes
open FStar.Mul
open NatPrime

open Hacl.Spec.Poly1305.Field32.Lemmas

include Hacl.Spec.Poly1305.Field32.Definition

#reset-options "--z3rlimit 50 --max_fuel 0 --using_facts_from '* -FStar.Seq'"

inline_for_extraction
val fadd5:
    f1:felem5{felem_fits5 f1 (1, 2, 1, 1, 1)}
  -> f2:felem5{felem_fits5 f2 (1, 1, 1, 1, 1)}
  -> out:felem5{felem_fits5 f2 (2, 3, 2, 2, 2) /\
      feval out == fadd (feval f1) (feval f2)}
let fadd5 (f10, f11, f12, f13, f14) (f20, f21, f22, f23, f24) =
  [@inline_let]
  let o0 = f10 +! f20 in
  [@inline_let]
  let o1 = f11 +! f21 in
  [@inline_let]
  let o2 = f12 +! f22 in
  [@inline_let]
  let o3 = f13 +! f23 in
  [@inline_let]
  let o4 = f14 +! f24 in
  FStar.Math.Lemmas.lemma_mod_plus_distr_l
    (as_nat5 (f10, f11, f12, f13, f14)) (as_nat5 (f20, f21, f22, f23, f24)) prime;
  FStar.Math.Lemmas.lemma_mod_plus_distr_r
    ((as_nat5 (f10, f11, f12, f13, f14)) % prime) (as_nat5 (f20, f21, f22, f23, f24)) prime;
  (o0, o1, o2, o3, o4)

inline_for_extraction
val mul_wide32:
    #m1:scale32
  -> #m2:scale32
  -> x:uint32{felem_fits1 x m1}
  -> y:uint32{felem_fits1 y m2 /\ m1 * m2 <= 4096}
  -> z:uint64{uint_v z == uint_v x * uint_v y /\ felem_wide_fits1 z (m1 * m2)}
let mul_wide32 #m1 #m2 x y =
  assert (v x * v y <= m1 * max26 * m2 * max26);
  assert (v x * v y <= m1 * m2 * max26 * max26);
  to_u64 x *! to_u64 y

inline_for_extraction
val smul_felem5:
    #m1:scale32
  -> #m2:scale32_5
  -> u1:uint32{felem_fits1 u1 m1}
  -> f2:felem5{felem_fits5 f2 m2}
  -> out:felem_wide5{felem_wide_fits5 out (m1 *^ m2) /\
      wide_as_nat5 out == uint_v u1 * as_nat5 f2}
let smul_felem5 #m1 #m2 u1 (f20,f21,f22,f23,f24) =
  let (m20, m21, m22, m23, m24) = m2 in
  [@inline_let]
  let o0 = mul_wide32 #m1 #m20 u1 f20 in
  [@inline_let]
  let o1 = mul_wide32 #m1 #m21 u1 f21 in
  [@inline_let]
  let o2 = mul_wide32 #m1 #m22 u1 f22 in
  [@inline_let]
  let o3 = mul_wide32 #m1 #m23 u1 f23 in
  [@inline_let]
  let o4 = mul_wide32 #m1 #m24 u1 f24 in
  lemma_smul_felem5 #m1 #m2 u1 (f20,f21,f22,f23,f24);
  (o0, o1, o2, o3, o4)

inline_for_extraction
val mul_add_wide64:
    #m1:scale32
  -> #m2:scale32
  -> #m3:scale64
  -> x:uint32{felem_fits1 x m1}
  -> y:uint32{felem_fits1 y m2}
  -> z:uint64{felem_wide_fits1 z m3 /\ m3 + m1 * m2 <= 4096}
  -> r:uint64{uint_v r == uint_v z + uint_v x * uint_v y /\ felem_wide_fits1 r (m3 + m1 * m2)}
let mul_add_wide64 #m1 #m2 #m3 x y z =
  z +! mul_wide32 #m1 #m2 x y

inline_for_extraction
val smul_add_felem5:
    #m1:scale32
  -> #m2:scale32_5
  -> #m3:scale64_5
  -> u1:uint32{felem_fits1 u1 m1}
  -> f2:felem5{felem_fits5 f2 m2}
  -> acc1:felem_wide5{felem_wide_fits5 acc1 m3 /\ m3 +* m1 *^ m2 <=* s64x5 4096}
  -> acc2:felem_wide5{
      wide_as_nat5 acc2 == wide_as_nat5 acc1 + uint_v u1 * as_nat5 f2 /\
      felem_wide_fits5 acc2 (m3 +* m1 *^ m2)}
let smul_add_felem5 #m1 #m2 #m3 u1 (f20, f21, f22, f23, f24) (o0, o1, o2, o3, o4) =
  let (m20, m21, m22, m23, m24) = m2 in
  let (m30, m31, m32, m33, m34) = m3 in
  [@inline_let]
  let o0' = mul_add_wide64 #m1 #m20 #m30 u1 f20 o0 in
  [@inline_let]
  let o1' = mul_add_wide64 #m1 #m21 #m31 u1 f21 o1 in
  [@inline_let]
  let o2' = mul_add_wide64 #m1 #m22 #m32 u1 f22 o2 in
  [@inline_let]
  let o3' = mul_add_wide64 #m1 #m23 #m33 u1 f23 o3 in
  [@inline_let]
  let o4' = mul_add_wide64 #m1 #m24 #m34 u1 f24 o4 in
  [@inline_let]
  let out = (o0', o1', o2', o3', o4') in
  lemma_smul_add_felem5 #m1 #m2 #m3 u1 (f20, f21, f22, f23, f24) (o0, o1, o2, o3, o4);
  out

inline_for_extraction
val precomp_r5:
    r:felem5{felem_fits5 r (1, 1, 1, 1, 1)}
  -> r5:felem5{felem_fits5 r5 (5, 5, 5, 5 ,5)}
let precomp_r5 (r0, r1, r2, r3, r4) =
  let r50 = r0 *! u32 5 in
  let r51 = r1 *! u32 5 in
  let r52 = r2 *! u32 5 in
  let r53 = r3 *! u32 5 in
  let r54 = r4 *! u32 5 in
  (r50, r51, r52, r53, r54)

#reset-options "--z3rlimit 200"

inline_for_extraction
val mul_felem5:
    f1:felem5{felem_fits5 f1 (2, 3, 2, 2, 2)}
  -> r:felem5{felem_fits5 r (1, 1, 1, 1, 1)}
  -> r5:felem5{felem_fits5 r5 (5, 5, 5, 5, 5) /\ r5 == precomp_r5 r}
  -> out:felem_wide5{felem_wide_fits5 out (47, 35, 27, 19, 11) /\
      feval_wide out == fmul (feval f1) (feval r)}
let mul_felem5 (f10,f11,f12,f13,f14) (r0,r1,r2,r3,r4) (r50,r51,r52,r53,r54) =
  let (a0,a1,a2,a3,a4) = smul_felem5 #2 #(1,1,1,1,1) f10 (r0,r1,r2,r3,r4) in
  let (a0,a1,a2,a3,a4) = smul_add_felem5 #3 #(5,1,1,1,1) #(2,2,2,2,2) f11 (r54,r0,r1,r2,r3) (a0,a1,a2,a3,a4) in
  let (a0,a1,a2,a3,a4) = smul_add_felem5 #2 #(5,5,1,1,1) #(17,5,5,5,5) f12 (r53,r54,r0,r1,r2) (a0,a1,a2,a3,a4) in
  let (a0,a1,a2,a3,a4) = smul_add_felem5 #2 #(5,5,5,1,1) #(27,15,7,7,7) f13 (r52,r53,r54,r0,r1) (a0,a1,a2,a3,a4) in
  let (a0,a1,a2,a3,a4) = smul_add_felem5 #2 #(5,5,5,5,1) #(37,25,17,9,9) f14 (r51,r52,r53,r54,r0) (a0,a1,a2,a3,a4) in
  admit();
  (a0,a1,a2,a3,a4)

inline_for_extraction
val carry26:
    l:uint32
  -> cin:uint32
  -> Pure (uint32 & uint32)
    (requires felem_fits1 l 2 /\ felem_fits1 cin 62)
    (ensures fun (l0, l1) ->
      felem_fits1 l0 1 /\ uint_v l1 <= 64 /\
      v l + v cin == v l1 * pow2 26 + v l0)
let carry26 l cin =
  let l1 = l +! cin in
  lemma_carry26 l cin;
  (l1 &. mask26, l1 >>. 26ul)

inline_for_extraction
val carry26_wide:
    #m:scale64{m < 64}
  -> l:uint64{felem_wide_fits1 l m}
  -> cin:uint32{felem_fits1 cin 64}
  -> Pure (uint32 & uint32)
    (requires True)
    (ensures fun (l0, l1) ->
      v l + v cin == v l1 * pow2 26 + v l0 /\
      felem_fits1 l0 1 /\ felem_fits1 l1 (m + 1))
let carry26_wide #m l cin =
  let l1 = l +! to_u64 cin in
  lemma_carry26_wide #m l cin;
  (to_u32 l1 &. mask26, to_u32 (l1 >>. 26ul))

let acc_inv_t (acc:felem5) =
  let (o0, o1, o2, o3, o4) = acc in
  if v o1 >= pow2 26 then
    felem_fits5 acc (1, 2, 1, 1, 1) /\ v o1 % pow2 26 < 64
  else felem_fits5 acc (1, 1, 1, 1, 1)

inline_for_extraction
val carry_wide5:
    inp:felem_wide5{felem_wide_fits5 inp (47, 35, 27, 19, 11)}
  -> Pure felem5
    (requires True)
    (ensures fun out ->
      feval out == feval_wide inp /\ acc_inv_t out)
let carry_wide5 (i0, i1, i2, i3, i4) =
  assert_norm (47 < 64);
  assert_norm (64 < max26);
  let tmp0, c0 = carry26_wide #47 i0 (u32 0) in
  let tmp1, c1 = carry26_wide #35 i1 c0 in
  let tmp2, c2 = carry26_wide #27 i2 c1 in
  let tmp3, c3 = carry26_wide #19 i3 c2 in
  let tmp4, c4 = carry26_wide #11 i4 c3 in
  lemma_carry_wide5_simplify (i0, i1, i2, i3, i4) c0 c1 c2 c3 c4 tmp0 tmp1 tmp2 tmp3 tmp4;
  [@inline_let]
  let tmp0', c5 = carry26 tmp0 (c4 *! u32 5) in
  [@inline_let]
  let tmp1' = tmp1 +! c5 in
  lemma_acc_inv (tmp0', tmp1, tmp2, tmp3, tmp4) c5;
  (tmp0', tmp1', tmp2, tmp3, tmp4)

inline_for_extraction
val fmul_r5:
    f1:felem5
  -> p:(felem5 & felem5)
  -> Pure felem5
    (requires
     (let r, r5 = p in
      felem_fits5 f1 (2, 3, 2, 2, 2) /\
      felem_fits5 r (1, 1, 1, 1, 1) /\
      felem_fits5 r5 (5, 5, 5, 5, 5) /\
      r5 == precomp_r5 r))
    (ensures fun out ->
      acc_inv_t out /\
     (let r, r5 = p in
      feval out == fmul (feval f1) (feval r)))
let fmul_r5 (f10, f11, f12, f13, f14) ((r0, r1, r2, r3, r4), (r50, r51, r52, r53, r54)) =
  let (t0, t1, t2, t3, t4) = mul_felem5 (f10, f11, f12, f13, f14) (r0, r1, r2, r3, r4) (r50, r51, r52, r53, r54) in
  carry_wide5 (t0, t1, t2, t3, t4)

inline_for_extraction
val fadd_mul_r5:
    acc:felem5
  -> f1:felem5
  -> p:(felem5 & felem5)
  -> Pure felem5
    (requires
     (let r, r5 = p in
      felem_fits5 acc (1, 2, 1, 1, 1) /\
      felem_fits5 f1 (1, 1, 1, 1, 1) /\
      felem_fits5 r (1, 1, 1, 1, 1) /\
      felem_fits5 r5 (5, 5, 5, 5, 5) /\
      r5 == precomp_r5 r))
    (ensures fun out ->
      acc_inv_t out /\
     (let r, r5 = p in
      feval out == fmul (fadd (feval acc) (feval f1)) (feval r)))
let fadd_mul_r5 (a0, a1, a2, a3, a4) (f10, f11, f12, f13, f14) ((r0, r1, r2, r3, r4), (r50, r51, r52, r53, r54)) =
  let (a0, a1, a2, a3, a4) = fadd5 (a0, a1, a2, a3, a4) (f10, f11, f12, f13, f14) in
  let (t0, t1, t2, t3, t4) = mul_felem5 (a0, a1, a2, a3, a4) (r0, r1, r2, r3, r4) (r50, r51, r52, r53, r54) in
  carry_wide5 (t0, t1, t2, t3, t4)

inline_for_extraction
val carry_felem5_full:
    inp:felem5{acc_inv_t inp}
  -> out:felem5{feval inp == feval out /\ felem_fits5 out (1, 1, 1, 1, 1)}
let carry_felem5_full (f0, f1, f2, f3, f4) =
  let tmp0, c0 = carry26 f0 (u32 0) in
  let tmp1, c1 = carry26 f1 c0 in
  assert (if v f1 < pow2 26 then v tmp1 < pow2 26 else v tmp1 < 64);
  let tmp2, c2 = carry26 f2 c1 in
  let tmp3, c3 = carry26 f3 c2 in
  let tmp4, c4 = carry26 f4 c3 in
  lemma_carry_felem5_full_simplify (f0, f1, f2, f3, f4) c0 c1 c2 c3 c4 tmp0 tmp1 tmp2 tmp3 tmp4;
  [@inline_let]
  let tmp0', c5 = carry26 tmp0 (c4 *. u32 5) in
  //assert (if v f1 < pow2 26 then v c5 = 0 else v c5 <= 1);
  [@inline_let]
  let tmp1' = tmp1 +! c5 in
  (tmp0', tmp1', tmp2, tmp3, tmp4)

inline_for_extraction
val subtract_p5:
    f:felem5{felem_fits5 f (1, 1, 1, 1, 1)}
  -> out:felem5{as_nat5 out = feval f}
let subtract_p5 (f0, f1, f2, f3, f4) =
  let mask0 = eq_mask f4 (u32 0x3ffffff) in
  let mask1 = mask0 &. eq_mask f3 (u32 0x3ffffff) in
  let mask2 = mask1 &. eq_mask f2 (u32 0x3ffffff) in
  let mask3 = mask2 &. eq_mask f1 (u32 0x3ffffff) in
  let mask4 = mask3 &. gte_mask f0 (u32 0x3fffffb) in

  let p0 = mask4 &. u32 0x3fffffb in
  let p1 = mask4 &. u32 0x3ffffff in
  let p2 = mask4 &. u32 0x3ffffff in
  let p3 = mask4 &. u32 0x3ffffff in
  let p4 = mask4 &. u32 0x3ffffff in

  let f0' = f0 -. p0 in
  let f1' = f1 -. p1 in
  let f2' = f2 -. p2 in
  let f3' = f3 -. p3 in
  let f4' = f4 -. p4 in
  lemma_subtract_p5 (f0, f1, f2, f3, f4) (f0', f1', f2', f3', f4');
  (f0', f1', f2', f3', f4')

inline_for_extraction
val reduce_felem5:
    f:felem5{acc_inv_t f}
  -> out:felem5{as_nat5 out == feval f}
let reduce_felem5 (f0, f1, f2, f3, f4) =
  let (f0, f1, f2, f3, f4) = carry_felem5_full (f0, f1, f2, f3, f4) in
  subtract_p5 (f0, f1, f2, f3, f4)
