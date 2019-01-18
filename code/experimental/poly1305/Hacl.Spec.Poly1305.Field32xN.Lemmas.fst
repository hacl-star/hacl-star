module Hacl.Spec.Poly1305.Field32xN.Lemmas

open Lib.IntTypes
open Lib.IntVector
open Lib.Sequence
open FStar.Mul

open Hacl.Spec.Poly1305.Field32xN
open Hacl.Poly1305.Field32xN.Lemmas
module S = Hacl.Spec.Poly1305.Vec

#reset-options "--z3rlimit 100 --using_facts_from '* -FStar.Seq'"

// val precomp_r5_fits_lemma:
//     #w:lanes
//   -> r:felem5 w
//   -> Lemma
//     (requires felem_fits5 r (1, 1, 1, 1, 1))
//     (ensures  felem_fits5 (precomp_r5 #w r) (5, 5, 5, 5, 5))
//     [SMTPat (precomp_r5 #w r)]
// let precomp_r5_fits_lemma #w r = ()

val fadd5_fits_lemma:
    #w:lanes
  -> f1:felem5 w
  -> f2:felem5 w
  -> Lemma
    (requires felem_fits5 f1 (1,2,1,1,1) /\ felem_fits5 f2 (1,1,1,1,1))
    (ensures  felem_fits5 (fadd5 f1 f2) (2,3,2,2,2))
    [SMTPat (fadd5 f1 f2)]
let fadd5_fits_lemma #w f1 f2 =
  let (f10, f11, f12, f13, f14) = f1 in
  let (f20, f21, f22, f23, f24) = f2 in
  let o = fadd5 f1 f2 in
  vec_add_mod_lemma f10 f20;
  vec_add_mod_lemma f11 f21;
  vec_add_mod_lemma f12 f22;
  vec_add_mod_lemma f13 f23;
  vec_add_mod_lemma f14 f24

val fadd5_eval_lemma:
    #w:lanes
  -> f1:felem5 w
  -> f2:felem5 w
  -> Lemma
    (requires felem_fits5 f1 (1,2,1,1,1) /\ felem_fits5 f2 (1,1,1,1,1))
    (ensures  feval5 (fadd5 f1 f2) == map2 S.pfadd (feval5 f1) (feval5 f2))
    [SMTPat (fadd5 f1 f2)]
let fadd5_eval_lemma #w f1 f2 =
  let o = fadd5 f1 f2 in
  match w with
  | 1 ->
    fadd5_eval_lemma_i f1 f2 0;
    eq_intro (feval5 o) (map2 S.pfadd (feval5 f1) (feval5 f2))
  | 2 ->
    fadd5_eval_lemma_i f1 f2 0;
    fadd5_eval_lemma_i f1 f2 1;
    eq_intro (feval5 o) (map2 S.pfadd (feval5 f1) (feval5 f2))
  | 4 ->
    fadd5_eval_lemma_i f1 f2 0;
    fadd5_eval_lemma_i f1 f2 1;
    fadd5_eval_lemma_i f1 f2 2;
    fadd5_eval_lemma_i f1 f2 3;
    eq_intro (feval5 o) (map2 S.pfadd (feval5 f1) (feval5 f2))

val smul_felem5_fits_lemma1:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32
  -> u1:uint64xN w
  -> f2:uint64xN w
  -> Lemma
    (requires felem_fits1 u1 m1 /\ felem_fits1 f2 m2)
    (ensures felem_wide_fits1 (vec_mul_mod f2 u1) (m1 * m2))
let smul_felem5_fits_lemma1 #w #m1 #m2 u1 f2 =
  match w with
  | 1 ->
    smul_felem5_fits_lemma_i #w #m1 #m2 u1 f2 0
  | 2 ->
    smul_felem5_fits_lemma_i #w #m1 #m2 u1 f2 0;
    smul_felem5_fits_lemma_i #w #m1 #m2 u1 f2 1
  | 4 ->
    smul_felem5_fits_lemma_i #w #m1 #m2 u1 f2 0;
    smul_felem5_fits_lemma_i #w #m1 #m2 u1 f2 1;
    smul_felem5_fits_lemma_i #w #m1 #m2 u1 f2 2;
    smul_felem5_fits_lemma_i #w #m1 #m2 u1 f2 3

val smul_felem5_fits_lemma:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32_5
  -> u1:uint64xN w
  -> f2:felem5 w
  -> Lemma
    (requires felem_fits1 u1 m1 /\ felem_fits5 f2 m2)
    (ensures  felem_wide_fits5 (smul_felem5 #w u1 f2) (m1 *^ m2))
let smul_felem5_fits_lemma #w #m1 #m2 u1 f2 =
  let (f20, f21, f22, f23, f24) = f2 in
  let (m20, m21, m22, m23, m24) = m2 in
  smul_felem5_fits_lemma1 #w #m1 #m20 u1 f20;
  smul_felem5_fits_lemma1 #w #m1 #m21 u1 f21;
  smul_felem5_fits_lemma1 #w #m1 #m22 u1 f22;
  smul_felem5_fits_lemma1 #w #m1 #m23 u1 f23;
  smul_felem5_fits_lemma1 #w #m1 #m24 u1 f24

val smul_felem5_eval_lemma:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32_5
  -> u1:uint64xN w
  -> f2:felem5 w
  -> Lemma
    (requires felem_fits1 u1 m1 /\ felem_fits5 f2 m2)
    (ensures
      fas_nat5 (smul_felem5 #w u1 f2) ==
      map2 #nat #nat #nat (fun a b -> a * b) (uint64xN_v u1) (fas_nat5 f2))
let smul_felem5_eval_lemma #w #m1 #m2 u1 f2 =
  match w with
  | 1 ->
    smul_felem5_eval_lemma_i #w #m1 #m2 u1 f2 0;
    eq_intro (fas_nat5 (smul_felem5 #w u1 f2))
      (map2 #nat #nat #nat (fun a b -> a * b) (uint64xN_v u1) (fas_nat5 f2))
  | 2 ->
    smul_felem5_eval_lemma_i #w #m1 #m2 u1 f2 0;
    smul_felem5_eval_lemma_i #w #m1 #m2 u1 f2 1;
    eq_intro (fas_nat5 (smul_felem5 #w u1 f2))
      (map2 #nat #nat #nat (fun a b -> a * b) (uint64xN_v u1) (fas_nat5 f2))
  | 4 ->
    smul_felem5_eval_lemma_i #w #m1 #m2 u1 f2 0;
    smul_felem5_eval_lemma_i #w #m1 #m2 u1 f2 1;
    smul_felem5_eval_lemma_i #w #m1 #m2 u1 f2 2;
    smul_felem5_eval_lemma_i #w #m1 #m2 u1 f2 3;
    eq_intro (fas_nat5 (smul_felem5 #w u1 f2))
      (map2 #nat #nat #nat (fun a b -> a * b) (uint64xN_v u1) (fas_nat5 f2))

val smul_add_felem5_fits_lemma1:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32
  -> #m3:scale64
  -> u1:uint64xN w
  -> f2:uint64xN w
  -> acc1:uint64xN w
  -> Lemma
    (requires
      felem_fits1 u1 m1 /\ felem_fits1 f2 m2 /\
      felem_wide_fits1 acc1 m3 /\ m3 + m1 * m2 <= 4096)
    (ensures felem_wide_fits1 (vec_add_mod acc1 (vec_mul_mod f2 u1)) (m3 + m1 * m2))
let smul_add_felem5_fits_lemma1 #w #m1 #m2 #m3 u1 f2 acc1 =
  match w with
  | 1 ->
    smul_add_felem5_fits_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 0
  | 2 ->
    smul_add_felem5_fits_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 0;
    smul_add_felem5_fits_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 1
  | 4 ->
    smul_add_felem5_fits_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 0;
    smul_add_felem5_fits_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 1;
    smul_add_felem5_fits_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 2;
    smul_add_felem5_fits_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 3

val smul_add_felem5_fits_lemma:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32_5
  -> #m3:scale64_5
  -> u1:uint64xN w
  -> f2:felem5 w
  -> acc1:felem_wide5 w
  -> Lemma
    (requires
      felem_fits1 u1 m1 /\ felem_fits5 f2 m2 /\
      felem_wide_fits5 acc1 m3 /\ m3 +* m1 *^ m2 <=* s64x5 4096)
    (ensures
      felem_wide_fits5 (smul_add_felem5 #w u1 f2 acc1) (m3 +* m1 *^ m2))
let smul_add_felem5_fits_lemma #w #m1 #m2 #m3 u1 f2 acc1 =
  let (f20, f21, f22, f23, f24) = f2 in
  let (m20, m21, m22, m23, m24) = m2 in
  let (a0, a1, a2, a3, a4) = acc1 in
  let (m30, m31, m32, m33, m34) = m3 in
  smul_add_felem5_fits_lemma1 #w #m1 #m20 #m30 u1 f20 a0;
  smul_add_felem5_fits_lemma1 #w #m1 #m21 #m31 u1 f21 a1;
  smul_add_felem5_fits_lemma1 #w #m1 #m22 #m32 u1 f22 a2;
  smul_add_felem5_fits_lemma1 #w #m1 #m23 #m33 u1 f23 a3;
  smul_add_felem5_fits_lemma1 #w #m1 #m24 #m34 u1 f24 a4

val smul_add_felem5_eval_lemma:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32_5
  -> #m3:scale64_5
  -> u1:uint64xN w
  -> f2:felem5 w
  -> acc1:felem_wide5 w
  -> Lemma
    (requires
      felem_fits1 u1 m1 /\
      felem_fits5 f2 m2 /\
      felem_wide_fits5 acc1 m3 /\
      m3 +* m1 *^ m2 <=* s64x5 4096)
    (ensures
      fas_nat5 (smul_add_felem5 #w u1 f2 acc1) ==
	map2 #nat #nat #nat (fun a b -> a + b) (fas_nat5 acc1)
	  (map2 #nat #nat #nat (fun a b -> a * b) (uint64xN_v u1) (fas_nat5 f2)))
let smul_add_felem5_eval_lemma #w #m1 #m2 #m3 u1 f2 acc1 =
  let tmp =
    map2 #nat #nat #nat (fun a b -> a + b) (fas_nat5 acc1)
      (map2 #nat #nat #nat (fun a b -> a * b) (uint64xN_v u1) (fas_nat5 f2)) in

  match w with
  | 1 ->
    smul_add_felem5_eval_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 0;
    eq_intro (fas_nat5 (smul_add_felem5 #w u1 f2 acc1)) tmp
  | 2 ->
    smul_add_felem5_eval_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 0;
    smul_add_felem5_eval_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 1;
    eq_intro (fas_nat5 (smul_add_felem5 #w u1 f2 acc1)) tmp
  | 4 ->
    smul_add_felem5_eval_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 0;
    smul_add_felem5_eval_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 1;
    smul_add_felem5_eval_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 2;
    smul_add_felem5_eval_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 3;
    eq_intro (fas_nat5 (smul_add_felem5 #w u1 f2 acc1)) tmp

val mul_felem5_fits_lemma:
    #w:lanes
  -> f1:felem5 w
  -> r:felem5 w
  -> r5:felem5 w
  -> Lemma
    (requires
      felem_fits5 f1 (2, 3, 2, 2, 2) /\
      felem_fits5 r (1, 2, 1, 1, 1) /\
      felem_fits5 r5 (5, 10, 5, 5, 5))
    (ensures
      felem_wide_fits5 (mul_felem5 #w f1 r r5) (57, 37, 30, 21, 13))
    [SMTPat (mul_felem5 #w f1 r r5)]
let mul_felem5_fits_lemma #w f1 r r5 =
  let (r0, r1, r2, r3, r4) = r in
  let (f10, f11, f12, f13, f14) = f1 in
  let (r50, r51, r52, r53, r54) = r5 in

  let (a0,a1,a2,a3,a4) = smul_felem5 #w f10 (r0,r1,r2,r3,r4) in
  smul_felem5_fits_lemma #w #2 #(1,2,1,1,1) f10 (r0,r1,r2,r3,r4);
  let (a10,a11,a12,a13,a14) = smul_add_felem5 #w f11 (r54,r0,r1,r2,r3) (a0,a1,a2,a3,a4) in
  smul_add_felem5_fits_lemma #w #3 #(5,1,2,1,1) #(2,4,2,2,2) f11 (r54,r0,r1,r2,r3) (a0,a1,a2,a3,a4);
  let (a20,a21,a22,a23,a24) = smul_add_felem5 #w f12 (r53,r54,r0,r1,r2) (a10,a11,a12,a13,a14) in
  smul_add_felem5_fits_lemma #w #2 #(5,5,1,2,1) #(17,7,8,5,5) f12 (r53,r54,r0,r1,r2) (a10,a11,a12,a13,a14);
  let (a30,a31,a32,a33,a34) = smul_add_felem5 #w f13 (r52,r53,r54,r0,r1) (a20,a21,a22,a23,a24) in
  smul_add_felem5_fits_lemma #w #2 #(5,5,5,1,2) #(27,17,10,9,7) f13 (r52,r53,r54,r0,r1) (a20,a21,a22,a23,a24);
  let (a40,a41,a42,a43,a44) = smul_add_felem5 #w f14 (r51,r52,r53,r54,r0) (a30,a31,a32,a33,a34) in
  smul_add_felem5_fits_lemma #w #2 #(10,5,5,5,1) #(37,27,20,11,11) f14 (r51,r52,r53,r54,r0) (a30,a31,a32,a33,a34)

val mul_felem5_eval_lemma_i:
    #w:lanes
  -> f1:felem5 w
  -> r:felem5 w
  -> r5:felem5 w
  -> i:nat{i < w}
  -> Lemma
    (requires
      felem_fits5 f1 (2, 3, 2, 2, 2) /\
      felem_fits5 r (1, 2, 1, 1, 1) /\
      felem_fits5 r5 (5, 10, 5, 5, 5) /\
      r5 == precomp_r5 r)
    (ensures
      (feval5 (mul_felem5 #w f1 r r5)).[i] == (feval5 f1).[i] `S.pfmul` (feval5 r).[i])
let mul_felem5_eval_lemma_i #w f1 r r5 i =
  let (r0, r1, r2, r3, r4) = r in
  let (f10, f11, f12, f13, f14) = f1 in
  let (r50, r51, r52, r53, r54) = r5 in

  let (a0,a1,a2,a3,a4) = smul_felem5 #w f10 (r0,r1,r2,r3,r4) in
  smul_felem5_eval_lemma #w #2 #(1,2,1,1,1) f10 (r0,r1,r2,r3,r4);
  smul_felem5_fits_lemma #w #2 #(1,2,1,1,1) f10 (r0,r1,r2,r3,r4);
  assert ((fas_nat5 (a0,a1,a2,a3,a4)).[i] == (uint64xN_v f10).[i] * (fas_nat5 (r0,r1,r2,r3,r4)).[i]);
  let (a10,a11,a12,a13,a14) = smul_add_felem5 #w f11 (r54,r0,r1,r2,r3) (a0,a1,a2,a3,a4) in
  smul_add_felem5_eval_lemma #w #3 #(5,1,2,1,1) #(2,4,2,2,2) f11 (r54,r0,r1,r2,r3) (a0,a1,a2,a3,a4);
  smul_add_felem5_fits_lemma #w #3 #(5,1,2,1,1) #(2,4,2,2,2) f11 (r54,r0,r1,r2,r3) (a0,a1,a2,a3,a4);
  assert ((fas_nat5 (a10,a11,a12,a13,a14)).[i] == (fas_nat5 (a0,a1,a2,a3,a4)).[i] + (uint64xN_v f11).[i] * (fas_nat5 (r54,r0,r1,r2,r3)).[i]);
  let (a20,a21,a22,a23,a24) = smul_add_felem5 #w f12 (r53,r54,r0,r1,r2) (a10,a11,a12,a13,a14) in
  smul_add_felem5_eval_lemma #w #2 #(5,5,1,2,1) #(17,7,8,5,5) f12 (r53,r54,r0,r1,r2) (a10,a11,a12,a13,a14);
  smul_add_felem5_fits_lemma #w #2 #(5,5,1,2,1) #(17,7,8,5,5) f12 (r53,r54,r0,r1,r2) (a10,a11,a12,a13,a14);
  assert ((fas_nat5 (a20,a21,a22,a23,a24)).[i] == (fas_nat5 (a10,a11,a12,a13,a14)).[i] + (uint64xN_v f12).[i] * (fas_nat5 (r53,r54,r0,r1,r2)).[i]);
  let (a30,a31,a32,a33,a34) = smul_add_felem5 #w f13 (r52,r53,r54,r0,r1) (a20,a21,a22,a23,a24) in
  smul_add_felem5_eval_lemma #w #2 #(5,5,5,1,2) #(27,17,10,9,7) f13 (r52,r53,r54,r0,r1) (a20,a21,a22,a23,a24);
  smul_add_felem5_fits_lemma #w #2 #(5,5,5,1,2) #(27,17,10,9,7) f13 (r52,r53,r54,r0,r1) (a20,a21,a22,a23,a24);
  assert ((fas_nat5 (a30,a31,a32,a33,a34)).[i] == (fas_nat5 (a20,a21,a22,a23,a24)).[i] + (uint64xN_v f13).[i] * (fas_nat5 (r52,r53,r54,r0,r1)).[i]);
  let (a40,a41,a42,a43,a44) = smul_add_felem5 #w f14 (r51,r52,r53,r54,r0) (a30,a31,a32,a33,a34) in
  smul_add_felem5_eval_lemma #w #2 #(10,5,5,5,1) #(37,27,20,11,11) f14 (r51,r52,r53,r54,r0) (a30,a31,a32,a33,a34);
  smul_add_felem5_fits_lemma #w #2 #(10,5,5,5,1) #(37,27,20,11,11) f14 (r51,r52,r53,r54,r0) (a30,a31,a32,a33,a34);
  assert ((fas_nat5 (a40,a41,a42,a43,a44)).[i] == (fas_nat5 (a30,a31,a32,a33,a34)).[i] + (uint64xN_v f14).[i] * (fas_nat5 (r51,r52,r53,r54,r0)).[i]);

  assert ((fas_nat5 (a40,a41,a42,a43,a44)).[i] ==
    (uint64xN_v f10).[i] * (fas_nat5 (r0,r1,r2,r3,r4)).[i] +
    (uint64xN_v f11).[i] * (fas_nat5 (r54,r0,r1,r2,r3)).[i] +
    (uint64xN_v f12).[i] * (fas_nat5 (r53,r54,r0,r1,r2)).[i] +
    (uint64xN_v f13).[i] * (fas_nat5 (r52,r53,r54,r0,r1)).[i] +
    (uint64xN_v f14).[i] * (fas_nat5 (r51,r52,r53,r54,r0)).[i]);
  mul_felem5_eval_as_tup64 #w f1 r r5 i;
  mul_felem5_lemma (as_tup64_i f1 i) (as_tup64_i r i)

val mul_felem5_eval_lemma:
    #w:lanes
  -> f1:felem5 w
  -> r:felem5 w
  -> r5:felem5 w
  -> Lemma
    (requires
      felem_fits5 f1 (2, 3, 2, 2, 2) /\
      felem_fits5 r (1, 2, 1, 1, 1) /\
      felem_fits5 r5 (5, 10, 5, 5, 5) /\
      r5 == precomp_r5 r)
    (ensures
      feval5 (mul_felem5 #w f1 r r5) == map2 (S.pfmul) (feval5 f1) (feval5 r))
    [SMTPat (mul_felem5 #w f1 r r5)]
let mul_felem5_eval_lemma #w f1 r r5 =
  let tmp = map2 (S.pfmul) (feval5 f1) (feval5 r) in
  match w with
  | 1 ->
    mul_felem5_eval_lemma_i #w f1 r r5 0;
    eq_intro (feval5 (mul_felem5 #w f1 r r5)) tmp
  | 2 ->
    mul_felem5_eval_lemma_i #w f1 r r5 0;
    mul_felem5_eval_lemma_i #w f1 r r5 1;
    eq_intro (feval5 (mul_felem5 #w f1 r r5)) tmp
  | 4 ->
    mul_felem5_eval_lemma_i #w f1 r r5 0;
    mul_felem5_eval_lemma_i #w f1 r r5 1;
    mul_felem5_eval_lemma_i #w f1 r r5 2;
    mul_felem5_eval_lemma_i #w f1 r r5 3;
    eq_intro (feval5 (mul_felem5 #w f1 r r5)) tmp

val carry26_fits_lemma:
    #w:lanes
  -> l:uint64xN w
  -> cin:uint64xN w
  -> Lemma
    (requires felem_fits1 l 2 /\ felem_fits1 cin 62)
    (ensures
     (let (l0, l1) = carry26 #w l cin in
      felem_fits1 l0 1 /\ uint64xN_fits l1 64))
let carry26_fits_lemma #w l cin =
  match w with
  | 1 ->
    carry26_lemma_i #w l cin 0
  | 2 ->
    carry26_lemma_i #w l cin 0;
    carry26_lemma_i #w l cin 1
  | 4 ->
    carry26_lemma_i #w l cin 0;
    carry26_lemma_i #w l cin 1;
    carry26_lemma_i #w l cin 2;
    carry26_lemma_i #w l cin 3

val carry26_eval_lemma:
    #w:lanes
  -> l:uint64xN w
  -> cin:uint64xN w
  -> Lemma
    (requires felem_fits1 l 2 /\ felem_fits1 cin 62)
    (ensures
     (let (l0, l1) = carry26 #w l cin in
      felem_fits1 l0 1 /\ uint64xN_fits l1 64 /\
      (forall (i:nat). i < w ==>
	(uint64xN_v l).[i] + (uint64xN_v cin).[i] ==
        (uint64xN_v l1).[i] * pow2 26 + (uint64xN_v l0).[i])))
let carry26_eval_lemma #w l cin =
  match w with
  | 1 ->
    carry26_lemma_i #w l cin 0
  | 2 ->
    carry26_lemma_i #w l cin 0;
    carry26_lemma_i #w l cin 1
  | 4 ->
    carry26_lemma_i #w l cin 0;
    carry26_lemma_i #w l cin 1;
    carry26_lemma_i #w l cin 2;
    carry26_lemma_i #w l cin 3

val carry26_wide_fits_lemma:
    #w:lanes
  -> #m:scale64{m < 64}
  -> l:uint64xN w
  -> cin:uint64xN w
  -> Lemma
    (requires felem_wide_fits1 l m /\ felem_fits1 cin 64)
    (ensures
     (let (l0, l1) = carry26 #w l cin in
      felem_fits1 l0 1 /\ felem_fits1 l1 (m + 1)))
let carry26_wide_fits_lemma #w #m l cin =
  match w with
  | 1 ->
    carry26_wide_lemma_i #w #m l cin 0
  | 2 ->
    carry26_wide_lemma_i #w #m l cin 0;
    carry26_wide_lemma_i #w #m l cin 1
  | 4 ->
    carry26_wide_lemma_i #w #m l cin 0;
    carry26_wide_lemma_i #w #m l cin 1;
    carry26_wide_lemma_i #w #m l cin 2;
    carry26_wide_lemma_i #w #m l cin 3

val carry26_wide_eval_lemma:
    #w:lanes
  -> #m:scale64{m < 64}
  -> l:uint64xN w
  -> cin:uint64xN w
  -> Lemma
    (requires felem_wide_fits1 l m /\ felem_fits1 cin 64)
    (ensures
     (let (l0, l1) = carry26 #w l cin in
      felem_fits1 l0 1 /\ felem_fits1 l1 (m + 1) /\
       (forall (i:nat). i < w ==>
       (uint64xN_v l).[i] + (uint64xN_v cin).[i] ==
	(uint64xN_v l1).[i] * pow2 26 + (uint64xN_v l0).[i])))
let carry26_wide_eval_lemma #w #m l cin =
  match w with
  | 1 ->
    carry26_wide_lemma_i #w #m l cin 0
  | 2 ->
    carry26_wide_lemma_i #w #m l cin 0;
    carry26_wide_lemma_i #w #m l cin 1
  | 4 ->
    carry26_wide_lemma_i #w #m l cin 0;
    carry26_wide_lemma_i #w #m l cin 1;
    carry26_wide_lemma_i #w #m l cin 2;
    carry26_wide_lemma_i #w #m l cin 3

val carry_wide_felem5_fits_lemma:
    #w:lanes
  -> inp:felem_wide5 w
  -> Lemma
    (requires felem_wide_fits5 inp (57, 37, 30, 21, 13))
    (ensures acc_inv_t (carry_wide_felem5 #w inp))
let carry_wide_felem5_fits_lemma #w inp = admit()

val carry_wide_felem5_eval_lemma_i:
    #w:lanes
  -> inp:felem_wide5 w
  -> i:nat{i < w}
  -> Lemma
    (requires felem_wide_fits5 inp (57, 37, 30, 21, 13))
    (ensures (feval5 (carry_wide_felem5 #w inp)).[i] == (feval5 inp).[i])
let carry_wide_felem5_eval_lemma_i #w inp i = admit()

val carry_wide_felem5_eval_lemma:
    #w:lanes
  -> inp:felem_wide5 w
  -> Lemma
    (requires felem_wide_fits5 inp (57, 37, 30, 21, 13))
    (ensures feval5 (carry_wide_felem5 #w inp) == feval5 inp)
let carry_wide_felem5_eval_lemma #w inp =
  let o = carry_wide_felem5 #w inp in
  match w with
  | 1 ->
    carry_wide_felem5_eval_lemma_i #w inp 0;
    eq_intro (feval5 o) (feval5 inp)
  | 2 ->
    carry_wide_felem5_eval_lemma_i #w inp 0;
    carry_wide_felem5_eval_lemma_i #w inp 1;
    eq_intro (feval5 o) (feval5 inp)
  | 4 ->
    carry_wide_felem5_eval_lemma_i #w inp 0;
    carry_wide_felem5_eval_lemma_i #w inp 1;
    carry_wide_felem5_eval_lemma_i #w inp 2;
    carry_wide_felem5_eval_lemma_i #w inp 3;
    eq_intro (feval5 o) (feval5 inp)

val fmul_r5_fits_lemma:
    #w:lanes
  -> f1:felem5 w
  -> r:felem5 w
  -> r5:felem5 w
  -> Lemma
    (requires
      felem_fits5 f1 (2, 3, 2, 2, 2) /\
      felem_fits5 r (1, 2, 1, 1, 1) /\
      felem_fits5 r5 (5, 10, 5, 5, 5))
    (ensures
      acc_inv_t (fmul_r5 #w f1 r r5))
    [SMTPat (fmul_r5 #w f1 r r5)]
let fmul_r5_fits_lemma #w f1 r r5 =
  let tmp = mul_felem5 f1 r r5 in
  mul_felem5_fits_lemma #w f1 r r5;
  let res = carry_wide_felem5 tmp in
  carry_wide_felem5_fits_lemma #w tmp

val fmul_r5_eval_lemma:
    #w:lanes
  -> f1:felem5 w
  -> r:felem5 w
  -> r5:felem5 w
  -> Lemma
    (requires
      felem_fits5 f1 (2, 3, 2, 2, 2) /\
      felem_fits5 r (1, 2, 1, 1, 1) /\
      felem_fits5 r5 (5, 10, 5, 5, 5) /\
      r5 == precomp_r5 r)
    (ensures
      feval5 (fmul_r5 #w f1 r r5) == map2 (S.pfmul) (feval5 f1) (feval5 r))
    [SMTPat (fmul_r5 #w f1 r r5)]
let fmul_r5_eval_lemma #w f1 r r5 =
  let tmp = mul_felem5 f1 r r5 in
  mul_felem5_eval_lemma #w f1 r r5;
  let res = carry_wide_felem5 tmp in
  carry_wide_felem5_eval_lemma #w tmp

val fadd_mul_r5_fits_lemma:
    #w:lanes
  -> acc:felem5 w
  -> f1:felem5 w
  -> r:felem5 w
  -> r5:felem5 w
  -> Lemma
    (requires
      felem_fits5 acc (1, 2, 1, 1, 1) /\
      felem_fits5 f1 (1, 1, 1, 1, 1) /\
      felem_fits5 r (1, 1, 1, 1, 1) /\
      felem_fits5 r5 (5, 5, 5, 5, 5))
    (ensures
      acc_inv_t (fadd_mul_r5 acc f1 r r5))
    [SMTPat (fadd_mul_r5 acc f1 r r5)]
let fadd_mul_r5_fits_lemma #w acc f1 r r5 =
  let acc1 = fadd5 acc f1 in
  fadd5_fits_lemma #w acc f1;
  let tmp = mul_felem5 acc1 r r5 in
  mul_felem5_fits_lemma #w acc1 r r5;
  let res = carry_wide_felem5 tmp in
  carry_wide_felem5_fits_lemma #w tmp

val fadd_mul_r5_eval_lemma:
    #w:lanes
  -> acc:felem5 w
  -> f1:felem5 w
  -> r:felem5 w
  -> r5:felem5 w
  -> Lemma
    (requires
      felem_fits5 acc (1, 2, 1, 1, 1) /\
      felem_fits5 f1 (1, 1, 1, 1, 1) /\
      felem_fits5 r (1, 1, 1, 1, 1) /\
      felem_fits5 r5 (5, 5, 5, 5, 5) /\
      r5 == precomp_r5 r)
    (ensures
      feval5 (fadd_mul_r5 acc f1 r r5) ==
	map2 (S.pfmul) (map2 (S.pfadd) (feval5 acc) (feval5 f1)) (feval5 r))
    [SMTPat (fadd_mul_r5 acc f1 r r5)]
let fadd_mul_r5_eval_lemma #w acc f1 r r5 =
  let acc1 = fadd5 acc f1 in
  fadd5_eval_lemma #w acc f1;
  let tmp = mul_felem5 acc1 r r5 in
  mul_felem5_eval_lemma #w acc1 r r5;
  let res = carry_wide_felem5 tmp in
  carry_wide_felem5_eval_lemma #w tmp

val reduce_felem5_eval_lemma:
    #w:lanes
  -> f:felem5 w
  -> Lemma
    (requires acc_inv_t f)
    (ensures
      feval5 (reduce_felem5 f) == feval5 f /\
      felem_less5 (reduce_felem5 f) S.prime)
    [SMTPat (reduce_felem5 f)]
let reduce_felem5_eval_lemma #w f1 = admit()
