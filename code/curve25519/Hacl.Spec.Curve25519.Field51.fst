module Hacl.Spec.Curve25519.Field51

open Lib.Sequence
open Lib.IntTypes
open FStar.Mul
open Spec.Curve25519

open Hacl.Spec.Curve25519.Field51.Definition
open Hacl.Spec.Curve25519.Field51.Lemmas

#reset-options "--z3rlimit 50  --using_facts_from '* -FStar.Seq'"

inline_for_extraction noextract
val fadd5:
    f1:felem5{felem_fits5 f1 (1, 2, 1, 1, 1)}
  -> f2:felem5{felem_fits5 f2 (1, 2, 1, 1, 1)}
  -> out:felem5{felem_fits5 out (2, 4, 2, 2, 2) /\
      feval out == fadd (feval f1) (feval f2)}
let fadd5 (f10, f11, f12, f13, f14) (f20, f21, f22, f23, f24) =
  let o0 = f10 +! f20 in
  let o1 = f11 +! f21 in
  let o2 = f12 +! f22 in
  let o3 = f13 +! f23 in
  let o4 = f14 +! f24 in
  let out = (o0, o1, o2, o3, o4) in
  FStar.Math.Lemmas.lemma_mod_plus_distr_l
    (as_nat5 (f10, f11, f12, f13, f14)) (as_nat5 (f20, f21, f22, f23, f24)) prime;
  FStar.Math.Lemmas.lemma_mod_plus_distr_r
    ((as_nat5 (f10, f11, f12, f13, f14)) % prime) (as_nat5 (f20, f21, f22, f23, f24)) prime;
  out

inline_for_extraction noextract
val fadd_zero:
    f1:felem5{felem_fits5 f1 (1, 2, 1, 1, 1)}
  -> out:felem5{felem_fits5 out (9, 10, 9, 9, 9) /\
      feval out == feval f1}
let fadd_zero (f10, f11, f12, f13, f14) =
  let o0 = f10 +! u64 0x3fffffffffff68 in
  let o1 = f11 +! u64 0x3ffffffffffff8 in
  let o2 = f12 +! u64 0x3ffffffffffff8 in
  let o3 = f13 +! u64 0x3ffffffffffff8 in
  let o4 = f14 +! u64 0x3ffffffffffff8 in
  lemma_add_zero (f10, f11, f12, f13, f14);
  (o0, o1, o2, o3, o4)

inline_for_extraction noextract
val fsub5:
    f1:felem5{felem_fits5 f1 (1, 2, 1, 1, 1)}
  -> f2:felem5{felem_fits5 f2 (1, 2, 1, 1, 1)}
  -> out:felem5{felem_fits5 out (9, 10, 9, 9, 9) /\
    feval out == fsub (feval f1) (feval f2)}
let fsub5 (f10, f11, f12, f13, f14) (f20, f21, f22, f23, f24) =
  //assert_norm (0x3fffffffffff68 == pow2 54 - 152);
  //assert_norm (0x3ffffffffffff8 == pow2 54 - 8);
  let (t0, t1, t2, t3, t4) = fadd_zero (f10, f11, f12, f13, f14) in
  let o0 = t0 -! f20 in
  let o1 = t1 -! f21 in
  let o2 = t2 -! f22 in
  let o3 = t3 -! f23 in
  let o4 = t4 -! f24 in
  let out = (o0, o1, o2, o3, o4) in
  FStar.Math.Lemmas.lemma_mod_plus_distr_l
    (as_nat5 (t0, t1, t2, t3, t4)) (- as_nat5 (f20, f21, f22, f23, f24)) prime;
  lemma_mod_sub_distr ((as_nat5 (t0, t1, t2, t3, t4)) % prime) (as_nat5 (f20, f21, f22, f23, f24)) prime;
  out

val lemma_fsub:
    f1:felem5{felem_fits5 f1 (1, 2, 1, 1, 1)}
  -> f2:felem5{felem_fits5 f2 (1, 2, 1, 1, 1)}
  -> Lemma (let (f10, f11, f12, f13, f14) = f1 in
      let (f20, f21, f22, f23, f24) = f2 in
      let o0 = f10 +! u64 0x3fffffffffff68 -! f20 in
      let o1 = f11 +! u64 0x3ffffffffffff8 -! f21 in
      let o2 = f12 +! u64 0x3ffffffffffff8 -! f22 in
      let o3 = f13 +! u64 0x3ffffffffffff8 -! f23 in
      let o4 = f14 +! u64 0x3ffffffffffff8 -! f24 in
      let out = (o0, o1, o2, o3, o4) in
      out == fsub5 (f10, f11, f12, f13, f14) (f20, f21, f22, f23, f24))
let lemma_fsub f1 f2 = ()

inline_for_extraction noextract
val mul_wide64:
    #m1:scale64
  -> #m2:scale64
  -> x:uint64{felem_fits1 x m1}
  -> y:uint64{felem_fits1 y m2 /\ m1 * m2 <= 67108864}
  -> z:uint128{uint_v z == uint_v x * uint_v y /\ felem_wide_fits1 z (m1 * m2)}
let mul_wide64 #m1 #m2 x y =
  assert (v x * v y <= m1 * max51 * m2 * max51);
  assert (v x * v y <= m1 * m2 * max51 * max51);
  mul64_wide x y

inline_for_extraction noextract
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
  [@inline_let]
  let out = (o0, o1, o2, o3, o4) in
  lemma_smul_felem5 u1 (f20, f21, f22, f23, f24);
  out

inline_for_extraction noextract
val mul_add_wide128:
    #m1:scale64
  -> #m2:scale64
  -> #m3:scale128
  -> x:uint64{felem_fits1 x m1}
  -> y:uint64{felem_fits1 y m2}
  -> z:uint128{felem_wide_fits1 z m3 /\ m3 + m1 * m2 <= 67108864}
  -> r:uint128{uint_v r == uint_v z + uint_v x * uint_v y /\ felem_wide_fits1 r (m3 + m1 * m2)}
let mul_add_wide128 #m1 #m2 #m3 x y z =
  z +! mul_wide64 #m1 #m2 x y

inline_for_extraction noextract
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
  let o0' = mul_add_wide128 #m1 #m20 #m30 u1 f20 o0 in
  [@inline_let]
  let o1' = mul_add_wide128 #m1 #m21 #m31 u1 f21 o1 in
  [@inline_let]
  let o2' = mul_add_wide128 #m1 #m22 #m32 u1 f22 o2 in
  [@inline_let]
  let o3' = mul_add_wide128 #m1 #m23 #m33 u1 f23 o3 in
  [@inline_let]
  let o4' = mul_add_wide128 #m1 #m24 #m34 u1 f24 o4 in
  [@inline_let]
  let out = (o0', o1', o2', o3', o4') in
  lemma_smul_add_felem5 u1 (f20, f21, f22, f23, f24) (o0, o1, o2, o3, o4);
  out

inline_for_extraction noextract
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

inline_for_extraction noextract
val mul_felem5:
    f1:felem5{felem_fits5 f1 (9, 10, 9, 9, 9)}
  -> r:felem5{felem_fits5 r (9, 10, 9, 9, 9)}
  -> r19:felem5{felem_fits5 r19 (171, 190, 171, 171, 171) /\ r19 == precomp_r19 r}
  -> out:felem_wide5{felem_wide_fits5 out (6579, 4797, 3340, 1881, 423) /\
      feval_wide out == fmul (feval f1) (feval r)}
let mul_felem5 (f10, f11, f12, f13, f14) (r0, r1, r2, r3, r4) (r190, r191, r192, r193, r194) =
  let (o0, o1, o2, o3, o4) = smul_felem5 #9 #(9, 10, 9, 9, 9) f10 (r0, r1, r2, r3, r4) in
  let (o0, o1, o2, o3, o4) = smul_add_felem5 #10 #(171, 9, 10, 9, 9) #(81, 90, 81, 81, 81)
    f11 (r194, r0, r1, r2, r3) (o0, o1, o2, o3, o4) in
  let (o0, o1, o2, o3, o4) = smul_add_felem5 #9 #(171, 171, 9, 10, 9) #(1791, 180, 181, 171, 171)
    f12 (r193, r194, r0, r1, r2) (o0, o1, o2, o3, o4) in
  let (o0, o1, o2, o3, o4) = smul_add_felem5 #9 #(171, 171, 171, 9, 10) #(3330, 1719, 262, 261, 252)
    f13 (r192, r193, r194, r0, r1) (o0, o1, o2, o3, o4) in
  let (o0, o1, o2, o3, o4) = smul_add_felem5 #9 #(190, 171, 171, 171, 9) #(4869, 3258, 1801, 342, 342)
    f14 (r191, r192, r193, r194, r0) (o0, o1, o2, o3, o4) in
  lemma_fmul5 (f10, f11, f12, f13, f14) (r0, r1, r2, r3, r4);
  (o0, o1, o2, o3, o4)

inline_for_extraction noextract
val carry51:
    l:uint64
  -> cin:uint64
  -> Pure (uint64 & uint64)
    (requires felem_fits1 l 2 /\ felem_fits1 cin 8190)
    (ensures fun (l0, l1) ->
      v l + v cin == v l1 * pow2 51 + v l0 /\
      felem_fits1 l0 1 /\ uint_v l1 < pow2 13)
let carry51 l cin =
  let l' = l +! cin in
  lemma_carry51 l cin;
  (l' &. mask51, l' >>. 51ul)

inline_for_extraction noextract
val carry51_wide:
    #m:scale64{m < 8192}
  -> l:uint128{felem_wide_fits1 l m}
  -> cin:uint64
  -> Pure (uint64 & uint64)
    (requires True)
    (ensures fun (l0, l1) ->
      v l + v cin == v l1 * pow2 51 + v l0 /\
      felem_fits1 l0 1 /\ felem_fits1 l1 (m + 1))
let carry51_wide #m l cin =
  let l' = l +! to_u128 cin in
  lemma_carry51_wide #m l cin;
  ((to_u64 l') &. mask51, to_u64 (l' >>. 51ul))

let mul_inv_t (f:felem5) =
  let (o0, o1, o2, o3, o4) = f in
  if v o1 >= pow2 51 then
    felem_fits5 f (1, 2, 1, 1, 1) /\ v o1 % pow2 51 < 8192
  else felem_fits5 f (1, 1, 1, 1, 1)

val lemma_mul_inv:
    f:felem5{felem_fits5 f (1, 1, 1, 1, 1)}
  -> cin:uint64{v cin < pow2 51}
  -> Lemma
    (let (i0, i1, i2, i3, i4) = f in
    assert_norm (pow51 = pow2 51);
     let i1' = i1 +! cin in
     let out = (i0, i1', i2, i3, i4) in
     if (v i1 + v cin) / pow2 51 > 0 then
       felem_fits5 out (1, 2, 1, 1, 1) /\
       (v i1 + v cin) % pow2 51 < v cin
     else felem_fits5 out (1, 1, 1, 1, 1))
let lemma_mul_inv f cin =
  assert_norm (pow51 = pow2 51)

inline_for_extraction noextract
val carry_wide5:
    inp:felem_wide5{felem_wide_fits5 inp (6579, 4797, 3340, 1881, 423)}
  -> Pure felem5
    (requires True)
    (ensures fun out ->
      mul_inv_t out /\ feval out == feval_wide inp)
let carry_wide5 (i0, i1, i2, i3, i4) =
  assert_norm (6579 < pow2 13);
  assert_norm (pow2 13 < max51);
  let tmp0, c0 = carry51_wide #6579 i0 (u64 0) in
  let tmp1, c1 = carry51_wide #4797 i1 c0 in
  let tmp2, c2 = carry51_wide #3340 i2 c1 in
  let tmp3, c3 = carry51_wide #1881 i3 c2 in
  let tmp4, c4 = carry51_wide #423 i4 c3 in
  lemma_carry5_simplify c0 c1 c2 c3 c4 tmp0 tmp1 tmp2 tmp3 tmp4;

  let tmp0', c5 = carry51 tmp0 (c4 *! u64 19) in
  [@inline_let]
  let tmp1' = tmp1 +! c5 in
  lemma_mul_inv (tmp0', tmp1, tmp2, tmp3, tmp4) c5;
  (tmp0', tmp1', tmp2, tmp3, tmp4)

inline_for_extraction noextract
val fmul5:
    f1:felem5{felem_fits5 f1 (9, 10, 9, 9, 9)}
  -> f2:felem5{felem_fits5 f2 (9, 10, 9, 9, 9)}
  -> out:felem5{mul_inv_t out /\
    feval out == fmul (feval f1) (feval f2)}
let fmul5 (f10, f11, f12, f13, f14) (f20, f21, f22, f23, f24) =
  let (tmp0, tmp1, tmp2, tmp3, tmp4) = precomp_r19 (f20, f21, f22, f23, f24) in
  let (tmp_w0, tmp_w1, tmp_w2, tmp_w3, tmp_w4) =
    mul_felem5 (f10, f11, f12, f13, f14) (f20, f21, f22, f23, f24) (tmp0, tmp1, tmp2, tmp3, tmp4) in
  carry_wide5 (tmp_w0, tmp_w1, tmp_w2, tmp_w3, tmp_w4)

inline_for_extraction noextract
val fmul25:
    f1:felem5{felem_fits5 f1 (9, 10, 9, 9, 9)}
  -> f2:felem5{felem_fits5 f2 (9, 10, 9, 9, 9)}
  -> f3:felem5{felem_fits5 f3 (9, 10, 9, 9, 9)}
  -> f4:felem5{felem_fits5 f4 (9, 10, 9, 9, 9)}
  -> Pure (felem5 & felem5)
    (requires True)
    (ensures fun (out1, out2) ->
      mul_inv_t out1 /\ mul_inv_t out2 /\
      feval out1 == fmul (feval f1) (feval f2) /\
      feval out2 == fmul (feval f3) (feval f4))
let fmul25 (f10, f11, f12, f13, f14) (f20, f21, f22, f23, f24) (f30, f31, f32, f33, f34) (f40, f41, f42, f43, f44) =
  let (tmp10, tmp11, tmp12, tmp13, tmp14) = precomp_r19 (f20, f21, f22, f23, f24) in
  let (tmp20, tmp21, tmp22, tmp23, tmp24) = precomp_r19 (f40, f41, f42, f43, f44) in
  let (tmp_w10, tmp_w11, tmp_w12, tmp_w13, tmp_w14) =
    mul_felem5 (f10, f11, f12, f13, f14) (f20, f21, f22, f23, f24) (tmp10, tmp11, tmp12, tmp13, tmp14) in
  let (tmp_w20, tmp_w21, tmp_w22, tmp_w23, tmp_w24) =
    mul_felem5 (f30, f31, f32, f33, f34) (f40, f41, f42, f43, f44) (tmp20, tmp21, tmp22, tmp23, tmp24) in
  let (o10,o11,o12,o13,o14) = carry_wide5 (tmp_w10, tmp_w11, tmp_w12, tmp_w13, tmp_w14) in
  let (o20,o21,o22,o23,o24) = carry_wide5 (tmp_w20, tmp_w21, tmp_w22, tmp_w23, tmp_w24) in
  ((o10,o11,o12,o13,o14), (o20,o21,o22,o23,o24))

inline_for_extraction noextract
val fmul15:
    f1:felem5{felem_fits5 f1 (9, 10, 9, 9, 9)}
  -> f2:uint64{felem_fits1 f2 1}
  -> Pure felem5
    (requires True)
    (ensures fun out ->
      mul_inv_t out /\ feval out == (feval f1 * v f2) % prime)
let fmul15 (f10, f11, f12, f13, f14) f2 =
  let (tmp_w0, tmp_w1, tmp_w2, tmp_w3, tmp_w4) =
    smul_felem5 #1 #(9, 10, 9, 9, 9) f2 (f10, f11, f12, f13, f14) in
  let out = (tmp_w0, tmp_w1, tmp_w2, tmp_w3, tmp_w4) in
  [@inline_let]
  let res = carry_wide5 (tmp_w0, tmp_w1, tmp_w2, tmp_w3, tmp_w4) in
  FStar.Math.Lemmas.lemma_mod_mul_distr_l (as_nat5 (f10, f11, f12, f13, f14)) (uint_v f2) prime;
  res

// inline_for_extraction noextract
// val fsqr_felem5:
//     f:felem5{felem_fits5 f (9, 10, 9, 9, 9)}
//   -> out:felem_wide5{felem_wide_fits5 out (6579, 4797, 3340, 1881, 423)}
// let fsqr_felem5 (f0, f1, f2, f3, f4) =
//   let (o0, o1, o2, o3, o4) = smul_felem5 #9 #(9, 20, 18, 18, 18) f0 (f0, u64 2 *! f1, u64 2 *! f2, u64 2 *! f3, u64 2 *! f4) in
//   let (o0, o1, o2, o3, o4) = smul_add_felem5 #10 #(342, 0, 10, 18, 18) #(81, 180, 162, 162, 162)
//     f1 (u64 38 *! f4, u64 0, f1, u64 2 *! f2, u64 2 *! f3) (o0, o1, o2, o3, o4) in
//   let (o0, o1, o2, o3, o4) = smul_add_felem5 #9 #(342, 342, 0, 0, 9) #(3501, 180, 262, 342, 342)
//     f2 (u64 38 *! f3, u64 38 *! f4, u64 0, u64 0, f2) (o0, o1, o2, o3, o4) in
//   let (o0, o1, o2, o3, o4) = smul_add_felem5 #9 #(0, 171, 342, 0, 0) #(6579, 3258, 262, 342, 423)
//     f3 (u64 0, u64 19 *. f3, u64 38 *. f4, u64 0, u64 0) (o0, o1, o2, o3, o4) in
//   let (o0, o1, o2, o3, o4) = smul_add_felem5 #9 #(0, 0, 0, 171, 0) #(6579, 4797, 3340, 342, 423)
//     f4 (u64 0, u64 0, u64 0, u64 19 *. f4, u64 0) (o0, o1, o2, o3, o4) in
//   (o0, o1, o2, o3, o4)

#set-options "--z3rlimit 150 --max_fuel 0"

inline_for_extraction noextract
val fsqr_felem5:
    f:felem5{felem_fits5 f (9, 10, 9, 9, 9)}
  -> Pure felem_wide5
    (requires True)
    (ensures fun out ->
      felem_wide_fits5 out (6579, 4797, 3340, 1881, 423) /\
      feval_wide out == fmul (feval f) (feval f))
let fsqr_felem5 (f0, f1, f2, f3, f4) =
  let d0 = u64 2 *! f0 in
  let d1 = u64 2 *! f1 in
  let d2 = u64 38 *! f2 in
  let d3 = u64 19 *! f3 in
  let d419 = u64 19 *! f4 in
  let d4 = u64 2 *! d419 in
  assert_norm (6579 < pow2 13);
  mul64_wide_add3_lemma #9 #9 #342 #10 #342 #9 f0 f0 d4 f1 d2 f3;
  let s0 = mul64_wide f0 f0 +! mul64_wide d4 f1 +! mul64_wide d2 f3 in
  mul64_wide_add3_lemma #18 #10 #342 #9 #171 #9 d0 f1 d4 f2 d3 f3;
  let s1 = mul64_wide d0 f1 +! mul64_wide d4 f2 +! mul64_wide d3 f3 in
  mul64_wide_add3_lemma #18 #9 #10 #10 #342 #9 d0 f2 f1 f1 d4 f3;
  let s2 = mul64_wide d0 f2 +! mul64_wide f1 f1 +! mul64_wide d4 f3 in
  mul64_wide_add3_lemma #18 #9 #20 #9 #9 #171 d0 f3 d1 f2 f4 d419;
  let s3 = mul64_wide d0 f3 +! mul64_wide d1 f2 +! mul64_wide f4 d419 in
  mul64_wide_add3_lemma #18 #9 #20 #9 #9 #9 d0 f4 d1 f3 f2 f2;
  let s4 = mul64_wide d0 f4 +! mul64_wide d1 f3 +! mul64_wide f2 f2 in
  lemma_fmul_fsqr5 (f0, f1, f2, f3, f4);
  (s0, s1, s2, s3, s4)

inline_for_extraction noextract
val fsqr5:
    f:felem5{felem_fits5 f (9, 10, 9, 9, 9)}
  -> out:felem5{mul_inv_t out /\ feval out == fmul (feval f) (feval f)}
let fsqr5 (f0, f1, f2, f3, f4) =
  let (o0, o1, o2, o3, o4) = fsqr_felem5 (f0, f1, f2, f3, f4) in
  carry_wide5 (o0, o1, o2, o3, o4)

inline_for_extraction noextract
val fsqr25:
    f1:felem5{felem_fits5 f1 (9, 10, 9, 9, 9)}
  -> f2:felem5{felem_fits5 f2 (9, 10, 9, 9, 9)}
  -> Pure (felem5 & felem5)
    (requires True)
    (ensures fun (out1, out2) ->
      mul_inv_t out1 /\
      mul_inv_t out2 /\
      feval out1 == fmul (feval f1) (feval f1) /\
      feval out2 == fmul (feval f2) (feval f2))
let fsqr25 (f10, f11, f12, f13, f14) (f20, f21, f22, f23, f24) =
  let (o10, o11, o12, o13, o14) = fsqr_felem5 (f10, f11, f12, f13, f14) in
  let (o20, o21, o22, o23, o24) = fsqr_felem5 (f20, f21, f22, f23, f24) in
  let (o10, o11, o12, o13, o14) = carry_wide5 (o10, o11, o12, o13, o14) in
  let (o20, o21, o22, o23, o24) = carry_wide5 (o20, o21, o22, o23, o24) in
  ((o10, o11, o12, o13, o14), (o20, o21, o22, o23, o24))

#set-options "--z3rlimit 100 --max_fuel 2"

inline_for_extraction noextract
val carry_felem5_full:
    inp:felem5{mul_inv_t inp}
  -> out:felem5{feval out == feval inp /\ felem_fits5 out (1, 1, 1, 1, 1)}
let carry_felem5_full (f0, f1, f2, f3, f4) =
  assert_norm (pow51 = pow2 51);
  let tmp0, c0 = carry51 f0 (u64 0) in
  let tmp1, c1 = carry51 f1 c0 in
  assert (if v f1 < pow2 51 then v tmp1 < pow2 51 else v tmp1 < 8192);
  let tmp2, c2 = carry51 f2 c1 in
  let tmp3, c3 = carry51 f3 c2 in
  let tmp4, c4 = carry51 f4 c3 in
  lemma_carry5_simplify c0 c1 c2 c3 c4 tmp0 tmp1 tmp2 tmp3 tmp4;
  [@inline_let]
  let tmp0', c5 = carry51 tmp0 (c4 *! u64 19) in
  [@inline_let]
  let tmp1' = tmp1 +! c5 in
  (tmp0', tmp1', tmp2, tmp3, tmp4)

inline_for_extraction noextract
val subtract_p5:
    f:felem5{felem_fits5 f (1, 1, 1, 1, 1)}
  -> Pure felem5
    (requires True)
    (ensures fun out ->
      as_nat5 out == feval f /\
      felem_fits5 out (1, 1, 1, 1, 1) /\
      as_nat5 out < prime)
let subtract_p5 (f0, f1, f2, f3, f4) =
  let m0 = gte_mask f0 (u64 0x7ffffffffffed) in
  let m1 = eq_mask f1 (u64 0x7ffffffffffff) in
  let m2 = eq_mask f2 (u64 0x7ffffffffffff) in
  let m3 = eq_mask f3 (u64 0x7ffffffffffff) in
  let m4 = eq_mask f4 (u64 0x7ffffffffffff) in
  let mask = m0 &. m1 &. m2 &. m3 &. m4 in
  let f0' = f0 -. (mask &. u64 0x7ffffffffffed) in
  let f1' = f1 -. (mask &. u64 0x7ffffffffffff) in
  let f2' = f2 -. (mask &. u64 0x7ffffffffffff) in
  let f3' = f3 -. (mask &. u64 0x7ffffffffffff) in
  let f4' = f4 -. (mask &. u64 0x7ffffffffffff) in
  logand_lemma mask (u64 0x7ffffffffffed);
  logand_lemma mask (u64 0x7ffffffffffff);
  lemma_subtract_p (f0, f1, f2, f3, f4) (f0', f1', f2', f3', f4');
  (f0', f1', f2', f3', f4')

inline_for_extraction noextract
val store_felem5:
    f:felem5{mul_inv_t f}
  -> Pure (uint64 & uint64 & uint64 & uint64)
    (requires True)
    (ensures fun (o0, o1, o2, o3) ->
      feval f == v o0 + v o1 * pow2 64 +
      v o2 * pow2 64 * pow2 64 + v o3 * pow2 64 * pow2 64 * pow2 64)
let store_felem5 (f0, f1, f2, f3, f4) =
  let (f0, f1, f2, f3, f4) = carry_felem5_full (f0, f1, f2, f3, f4) in
  let (f0, f1, f2, f3, f4) = subtract_p5 (f0, f1, f2, f3, f4) in

  let o0 = f0 |. (f1 <<. 51ul) in
  let o1 = (f1 >>. 13ul) |. (f2 <<. 38ul) in
  let o2 = (f2 >>. 26ul) |. (f3 <<. 25ul) in
  let o3 = (f3 >>. 39ul) |. (f4 <<. 12ul) in
  lemma_store_felem (f0, f1, f2, f3, f4);
  (o0, o1, o2, o3)
