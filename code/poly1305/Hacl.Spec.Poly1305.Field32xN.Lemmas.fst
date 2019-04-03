module Hacl.Spec.Poly1305.Field32xN.Lemmas

open Lib.IntTypes
open Lib.IntVector
open Lib.Sequence
open FStar.Mul

open Hacl.Spec.Poly1305.Field32xN
open Hacl.Poly1305.Field32xN.Lemmas
open Hacl.Impl.Poly1305.Lemmas
module S = Hacl.Spec.Poly1305.Vec

#reset-options "--z3rlimit 100 --max_fuel 0 --using_facts_from '* -FStar.Seq'"

val lemma_feval_is_fas_nat_i:
  #w:lanes
  -> f:felem5 w
  -> i:size_nat{i < w}
  -> Lemma
    (requires felem_less5 f (pow2 128))
    (ensures (feval5 f).[i] == (fas_nat5 f).[i])
let lemma_feval_is_fas_nat_i #w f i =
  assert_norm (pow2 128 < S.prime);
  assert ((feval5 f).[i] == (as_nat5 (transpose f).[i]) % S.prime);
  FStar.Math.Lemmas.modulo_lemma (as_nat5 (transpose f).[i]) S.prime

val lemma_feval_is_fas_nat:
  #w:lanes
  -> f:felem5 w
  -> Lemma
    (requires felem_less5 f (pow2 128))
    (ensures  (forall (i:nat). i < w ==> (fas_nat5 f).[i] == (feval5 f).[i]))
let lemma_feval_is_fas_nat #w f =
  match w with
  | 1 ->
    lemma_feval_is_fas_nat_i #w f 0
  | 2 ->
    lemma_feval_is_fas_nat_i #w f 0;
    lemma_feval_is_fas_nat_i #w f 1
  | 4 ->
    lemma_feval_is_fas_nat_i #w f 0;
    lemma_feval_is_fas_nat_i #w f 1;
    lemma_feval_is_fas_nat_i #w f 2;
    lemma_feval_is_fas_nat_i #w f 3

val precomp_r5_fits_lemma:
    #w:lanes
  -> r:felem5 w
  -> Lemma
    (requires felem_fits5 r (1, 1, 1, 1, 1))
    (ensures  felem_fits5 (precomp_r5 #w r) (5, 5, 5, 5, 5))
    [SMTPat (precomp_r5 #w r)]
let precomp_r5_fits_lemma #w r =
  match w with
  | 1 ->
    precomp_r5_as_tup64 #w r 0
  | 2 ->
    precomp_r5_as_tup64 #w r 0;
    precomp_r5_as_tup64 #w r 1
  | 4 ->
    precomp_r5_as_tup64 #w r 0;
    precomp_r5_as_tup64 #w r 1;
    precomp_r5_as_tup64 #w r 2;
    precomp_r5_as_tup64 #w r 3

val precomp_r5_fits_lemma2:
    #w:lanes
  -> r:felem5 w
  -> Lemma
    (requires felem_fits5 r (1, 2, 1, 1, 1))
    (ensures  felem_fits5 (precomp_r5 #w r) (5, 10, 5, 5, 5))
    [SMTPat (precomp_r5 #w r)]
let precomp_r5_fits_lemma2 #w r =
  match w with
  | 1 ->
    precomp_r5_as_tup64 #w r 0
  | 2 ->
    precomp_r5_as_tup64 #w r 0;
    precomp_r5_as_tup64 #w r 1
  | 4 ->
    precomp_r5_as_tup64 #w r 0;
    precomp_r5_as_tup64 #w r 1;
    precomp_r5_as_tup64 #w r 2;
    precomp_r5_as_tup64 #w r 3

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

#set-options "--z3rlimit 300"

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
      felem_fits5 (reduce_felem5 f) (1, 1, 1, 1, 1) /\
      (feval5 f).[0] == (fas_nat5 (reduce_felem5 f)).[0])
    [SMTPat (reduce_felem5 f)]
let reduce_felem5_eval_lemma #w f =
  carry_reduce_felem5_lemma #w f;
  subtract_p5_felem5_lemma #w (carry_full_felem5 f)

val fmul_r2_normalize50:
    acc:felem5 2
  -> r:felem5 2
  -> r2:felem5 2
  -> Pure (felem5 2)
    (requires
      felem_fits5 acc (2, 3, 2, 2, 2) /\
      felem_fits5 r (1, 1, 1, 1, 1) /\
      felem_fits5 r2 (1, 2, 1, 1, 1) /\
      feval5 r2 == S.compute_r2 (feval5 r))
    (ensures (fun a ->
      let fr21 = create2 (feval5 r2).[0] (feval5 r).[0] in
      feval5 a == S.fmul (feval5 acc) fr21 /\
      felem_fits5 a (1, 2, 1, 1, 1)))
let fmul_r2_normalize50 (a0, a1, a2, a3, a4) (r0, r1, r2, r3, r4) (r20, r21, r22, r23, r24) =
  let r210 = vec_interleave_low r20 r0 in
  vec_interleave_low_lemma2 r20 r0;
  let r211 = vec_interleave_low r21 r1 in
  vec_interleave_low_lemma2 r21 r1;
  let r212 = vec_interleave_low r22 r2 in
  vec_interleave_low_lemma2 r22 r2;
  let r213 = vec_interleave_low r23 r3 in
  vec_interleave_low_lemma2 r23 r3;
  let r214 = vec_interleave_low r24 r4 in
  vec_interleave_low_lemma2 r24 r4;

  let acc = (a0, a1, a2, a3, a4) in
  let fr = (r0, r1, r2, r3, r4) in
  let fr2 = (r20, r21, r22, r23, r24) in
  assert ((feval5 fr2).[0] == S.pfmul ((feval5 fr).[0]) ((feval5 fr).[0]));

  let fr21 = (r210, r211, r212, r213, r214) in
  eq_intro (feval5 fr21) (create2 (feval5 fr2).[0] (feval5 fr).[0]);
  assert (feval5 fr21 == create2 (feval5 fr2).[0] (feval5 fr).[0]);

  assert (felem_fits5 fr21 (1, 2, 1, 1, 1));
  let fr215 = precomp_r5 #2 fr21 in
  let a = fmul_r5 #2 acc fr21 fr215 in
  fmul_r5_eval_lemma acc fr21 fr215;
  fmul_r5_fits_lemma acc fr21 fr215;
  assert (feval5 a == S.fmul (feval5 acc) (feval5 fr21));
  assert (felem_fits5 a (1, 2, 1, 1, 1));
  a

val fmul_r2_normalize51:
    a:felem5 2
  -> fa1:felem5 2
  -> Pure (felem5 2)
    (requires
      felem_fits5 a (1, 2, 1, 1, 1) /\
      felem_fits5 fa1 (1, 2, 1, 1, 1) /\
      feval5 fa1 == create2 (feval5 a).[1] (feval5 a).[1])
    (ensures (fun out ->
      (feval5 out).[0] == S.pfadd (feval5 a).[0] (feval5 a).[1] /\
      felem_fits5 out (2, 4, 2, 2, 2)))
let fmul_r2_normalize51 a fa1 =
  let (a0, a1, a2, a3, a4) = a in
  let (a10, a11, a12, a13, a14) = fa1 in
  let o0 = vec_add_mod a0 a10 in
  let o1 = vec_add_mod a1 a11 in
  let o2 = vec_add_mod a2 a12 in
  let o3 = vec_add_mod a3 a13 in
  let o4 = vec_add_mod a4 a14 in
  let out = (o0, o1, o2, o3, o4) in

  let (a0, a1, a2, a3, a4) = as_tup64_i a 0 in
  let (a10, a11, a12, a13, a14) = as_tup64_i fa1 0 in
  let (o0, o1, o2, o3, o4) = as_tup64_i out 0 in

  FStar.Math.Lemmas.modulo_lemma (v a0 + v a10) (pow2 64);
  FStar.Math.Lemmas.modulo_lemma (v a1 + v a11) (pow2 64);
  FStar.Math.Lemmas.modulo_lemma (v a2 + v a12) (pow2 64);
  FStar.Math.Lemmas.modulo_lemma (v a3 + v a13) (pow2 64);
  FStar.Math.Lemmas.modulo_lemma (v a4 + v a14) (pow2 64);
  assert (
    as_nat5 (o0, o1, o2, o3, o4) ==
    as_nat5 (a0, a1, a2, a3, a4) + as_nat5 (a10, a11, a12, a13, a14));
  FStar.Math.Lemmas.lemma_mod_plus_distr_l
    (as_nat5 (a0, a1, a2, a3, a4)) (as_nat5 (a10, a11, a12, a13, a14)) S.prime;
  FStar.Math.Lemmas.lemma_mod_plus_distr_r
    (as_nat5 (a0, a1, a2, a3, a4) % S.prime) (as_nat5 (a10, a11, a12, a13, a14)) S.prime;
  assert (felem_fits5 out (2, 4, 2, 2, 2));
  out

val fmul_r2_normalize5_lemma:
    acc:felem5 2
  -> r:felem5 2
  -> r2:felem5 2
  -> Lemma
    (requires
      felem_fits5 acc (2, 3, 2, 2, 2) /\
      felem_fits5 r (1, 1, 1, 1, 1) /\
      felem_fits5 r2 (1, 2, 1, 1, 1) /\
      feval5 r2 == S.compute_r2 (feval5 r))
    (ensures (
      let out = fmul_r2_normalize5 acc r r2 in
      acc_inv_t out /\
      (feval5 out).[0] == S.normalize_2 (feval5 acc) (feval5 r)))
  [SMTPat (fmul_r2_normalize5 acc r r2)]
let fmul_r2_normalize5_lemma acc r r2 =
  let a = fmul_r2_normalize50 acc r r2 in
  let (a0, a1, a2, a3, a4) = a in

  let a10 = vec_interleave_high a0 a0 in
  vec_interleave_high_lemma2 a0 a0;
  let a11 = vec_interleave_high a1 a1 in
  vec_interleave_high_lemma2 a1 a1;
  let a12 = vec_interleave_high a2 a2 in
  vec_interleave_high_lemma2 a2 a2;
  let a13 = vec_interleave_high a3 a3 in
  vec_interleave_high_lemma2 a3 a3;
  let a14 = vec_interleave_high a4 a4 in
  vec_interleave_high_lemma2 a4 a4;
  let fa1 = (a10, a11, a12, a13, a14) in
  eq_intro (feval5 fa1) (create2 (feval5 a).[1] (feval5 a).[1]);
  assert (feval5 fa1 == create2 (feval5 a).[1] (feval5 a).[1]);
  assert (felem_fits5 fa1 (1, 2, 1, 1, 1));

  let out = fmul_r2_normalize51 a fa1 in
  assert ((feval5 out).[0] == S.pfadd (feval5 a).[0] (feval5 a).[1]);

  let res = carry_full_felem5 out in
  carry_full_felem5_lemma out

val fmul_r4_normalize50:
    acc:felem5 4
  -> r:felem5 4
  -> r2:felem5 4
  -> r3:felem5 4
  -> r4:felem5 4
  -> Pure (felem5 4)
    (requires
      felem_fits5 acc (2, 3, 2, 2, 2) /\
      felem_fits5 r (1, 1, 1, 1, 1) /\
      felem_fits5 r2 (1, 2, 1, 1, 1) /\
      felem_fits5 r3 (1, 2, 1, 1, 1) /\
      felem_fits5 r4 (1, 2, 1, 1, 1) /\
      feval5 r2 == S.fmul (feval5 r) (feval5 r) /\
      feval5 r3 == S.fmul (feval5 r2) (feval5 r) /\
      feval5 r4 == S.compute_r4 (feval5 r))
    (ensures (fun out ->
      let fr4321 = create4 (feval5 r4).[0] (feval5 r3).[0] (feval5 r2).[0] (feval5 r).[0] in
      feval5 out == S.fmul (feval5 acc) fr4321 /\
      felem_fits5 out (1, 2, 1, 1, 1)))
let fmul_r4_normalize50 acc fr fr2 fr3 fr4 =
  let (r10, r11, r12, r13, r14) = fr in
  let (r20, r21, r22, r23, r24) = fr2 in
  let (r30, r31, r32, r33, r34) = fr3 in
  let (r40, r41, r42, r43, r44) = fr4 in
  let (a0, a1, a2, a3, a4) = acc in

  let v12120 = vec_interleave_low r20 r10 in
  vec_interleave_low_lemma_uint64_4 r20 r10;
  let v34340 = vec_interleave_low r40 r30 in
  vec_interleave_low_lemma_uint64_4 r40 r30;
  let r12340 = cast U64 4 (vec_interleave_low (cast U128 2 v34340) (cast U128 2 v12120)) in
  lemma_vec_interleave_low_cast_64_4 v34340 v12120;
  //assert (vec_v r12340 == create4 (vec_v r40).[0] (vec_v r30).[0] (vec_v r20).[0] (vec_v r10).[0]);

  let v12121 = vec_interleave_low r21 r11 in
  vec_interleave_low_lemma_uint64_4 r21 r11;
  let v34341 = vec_interleave_low r41 r31 in
  vec_interleave_low_lemma_uint64_4 r41 r31;
  let r12341 = cast U64 4 (vec_interleave_low (cast U128 2 v34341) (cast U128 2 v12121)) in
  lemma_vec_interleave_low_cast_64_4 v34341 v12121;

  let v12122 = vec_interleave_low r22 r12 in
  vec_interleave_low_lemma_uint64_4 r22 r12;
  let v34342 = vec_interleave_low r42 r32 in
  vec_interleave_low_lemma_uint64_4 r42 r32;
  let r12342 = cast U64 4 (vec_interleave_low (cast U128 2 v34342) (cast U128 2 v12122)) in
  lemma_vec_interleave_low_cast_64_4 v34342 v12122;

  let v12123 = vec_interleave_low r23 r13 in
  vec_interleave_low_lemma_uint64_4 r23 r13;
  let v34343 = vec_interleave_low r43 r33 in
  vec_interleave_low_lemma_uint64_4 r43 r33;
  let r12343 = cast U64 4 (vec_interleave_low (cast U128 2 v34343) (cast U128 2 v12123)) in
  lemma_vec_interleave_low_cast_64_4 v34343 v12123;

  let v12124 = vec_interleave_low r24 r14 in
  vec_interleave_low_lemma_uint64_4 r24 r14;
  let v34344 = vec_interleave_low r44 r34 in
  vec_interleave_low_lemma_uint64_4 r44 r34;
  let r12344 = cast U64 4 (vec_interleave_low (cast U128 2 v34344) (cast U128 2 v12124)) in
  lemma_vec_interleave_low_cast_64_4 v34344 v12124;

  let fr1234 = (r12340, r12341, r12342, r12343, r12344) in
  eq_intro (feval5 fr1234) (create4 (feval5 fr4).[0] (feval5 fr3).[0] (feval5 fr2).[0] (feval5 fr).[0]);

  let fr12345 = precomp_r5 #4 fr1234 in
  let out = fmul_r5 #4 acc fr1234 fr12345 in
  fmul_r5_eval_lemma acc fr1234 fr12345;
  fmul_r5_fits_lemma acc fr1234 fr12345;
  out

val lemma_fmul_r4_normalize51:
    #m:scale32{m <= 2}
  -> o:uint64xN 4{felem_fits1 o m}
  -> Lemma
    (let v00 = cast U64 4 (vec_interleave_high (cast U128 2 o) (cast U128 2 o)) in
    let v10 = vec_add_mod o v00 in
    let v20 = vec_add_mod v10 (vec_permute4 v10 1ul 1ul 1ul 1ul) in
    felem_fits1 v20 (4 * m) /\
    (uint64xN_v v20).[0] ==
    (uint64xN_v o).[0] + (uint64xN_v o).[1] + (uint64xN_v o).[2] + (uint64xN_v o).[3])
let lemma_fmul_r4_normalize51 #m o =
  let v00 = cast U64 4 (vec_interleave_high (cast U128 2 o) (cast U128 2 o)) in
  lemma_vec_interleave_high_cast_64_4 o o;
  let v10 = vec_add_mod o v00 in
  FStar.Math.Lemmas.modulo_lemma ((uint64xN_v o).[0] + (uint64xN_v v00).[0]) (pow2 64);
  FStar.Math.Lemmas.modulo_lemma ((uint64xN_v o).[1] + (uint64xN_v v00).[1]) (pow2 64);
  let v20 = vec_add_mod v10 (vec_permute4 v10 1ul 1ul 1ul 1ul) in
  FStar.Math.Lemmas.modulo_lemma ((uint64xN_v v10).[0] + (uint64xN_v v10).[1]) (pow2 64)

val lemma_fmul_r4_normalize51_expand:
    v2:felem5 4
  -> out:felem5 4
  -> Lemma
    (requires (
      let (v20, v21, v22, v23, v24) = v2 in
      let (o0, o1, o2, o3, o4) = out in
      (uint64xN_v v20).[0] == (uint64xN_v o0).[0] + (uint64xN_v o0).[1] + (uint64xN_v o0).[2] + (uint64xN_v o0).[3] /\
      (uint64xN_v v21).[0] == (uint64xN_v o1).[0] + (uint64xN_v o1).[1] + (uint64xN_v o1).[2] + (uint64xN_v o1).[3] /\
      (uint64xN_v v22).[0] == (uint64xN_v o2).[0] + (uint64xN_v o2).[1] + (uint64xN_v o2).[2] + (uint64xN_v o2).[3] /\
      (uint64xN_v v23).[0] == (uint64xN_v o3).[0] + (uint64xN_v o3).[1] + (uint64xN_v o3).[2] + (uint64xN_v o3).[3] /\
      (uint64xN_v v24).[0] == (uint64xN_v o4).[0] + (uint64xN_v o4).[1] + (uint64xN_v o4).[2] + (uint64xN_v o4).[3]))
    (ensures (
      let (v20, v21, v22, v23, v24) = v2 in
      let (o0, o1, o2, o3, o4) = out in
      (feval5 v2).[0] ==
      S.pfadd (S.pfadd (S.pfadd (feval5 out).[0] (feval5 out).[1]) (feval5 out).[2]) (feval5 out).[3]))
let lemma_fmul_r4_normalize51_expand v2 out =
  let (v20, v21, v22, v23, v24) = as_tup64_i v2 0 in
  let (o0, o1, o2, o3, o4) = out in
  assert (
    as_nat5 (v20, v21, v22, v23, v24) % S.prime ==
      (as_nat5 (as_tup64_i out 0) + as_nat5 (as_tup64_i out 1) +
      as_nat5 (as_tup64_i out 2) + as_nat5 (as_tup64_i out 3)) % S.prime);
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (as_nat5 (as_tup64_i out 0) + as_nat5 (as_tup64_i out 1))
    (as_nat5 (as_tup64_i out 2) + as_nat5 (as_tup64_i out 3)) S.prime;
  FStar.Math.Lemmas.modulo_distributivity (as_nat5 (as_tup64_i out 0)) (as_nat5 (as_tup64_i out 1)) S.prime;
  assert (
    (feval5 v2).[0] ==
      (((feval5 out).[0] + (feval5 out).[1]) % S.prime +
      as_nat5 (as_tup64_i out 2) + as_nat5 (as_tup64_i out 3)) % S.prime);
  FStar.Math.Lemmas.lemma_mod_plus_distr_l
    (((feval5 out).[0] + (feval5 out).[1]) % S.prime + as_nat5 (as_tup64_i out 2))
    (as_nat5 (as_tup64_i out 3)) S.prime;
  FStar.Math.Lemmas.lemma_mod_plus_distr_r
    (((feval5 out).[0] + (feval5 out).[1]) % S.prime) (as_nat5 (as_tup64_i out 2)) S.prime;
  assert (
    (feval5 v2).[0] ==
      ((((feval5 out).[0] + (feval5 out).[1]) % S.prime + (feval5 out).[2]) % S.prime +
      as_nat5 (as_tup64_i out 3)) % S.prime);
  FStar.Math.Lemmas.lemma_mod_plus_distr_r
    ((((feval5 out).[0] + (feval5 out).[1]) % S.prime + (feval5 out).[2]) % S.prime)
     (as_nat5 (as_tup64_i out 3)) S.prime

val fmul_r4_normalize51:
    a:felem5 4
  -> Pure (felem5 4)
    (requires felem_fits5 a (1, 2, 1, 1, 1))
    (ensures (fun res ->
      felem_fits5 res (4, 8, 4, 4, 4) /\
      (feval5 res).[0] ==
      S.pfadd (S.pfadd (S.pfadd (feval5 a).[0] (feval5 a).[1]) (feval5 a).[2]) (feval5 a).[3]))
let fmul_r4_normalize51 fa =
  let (o0, o1, o2, o3, o4) = fa in
  let v00 = cast U64 4 (vec_interleave_high (cast U128 2 o0) (cast U128 2 o0)) in
  let v10 = vec_add_mod o0 v00 in
  let v20 = vec_add_mod v10 (vec_permute4 v10 1ul 1ul 1ul 1ul) in
  lemma_fmul_r4_normalize51 #1 o0;

  let v01 = cast U64 4 (vec_interleave_high (cast U128 2 o1) (cast U128 2 o1)) in
  let v11 = vec_add_mod o1 v01 in
  let v21 = vec_add_mod v11 (vec_permute4 v11 1ul 1ul 1ul 1ul) in
  lemma_fmul_r4_normalize51 #2 o1;

  let v02 = cast U64 4 (vec_interleave_high (cast U128 2 o2) (cast U128 2 o2)) in
  let v12 = vec_add_mod o2 v02 in
  let v22 = vec_add_mod v12 (vec_permute4 v12 1ul 1ul 1ul 1ul) in
  lemma_fmul_r4_normalize51 #1 o2;

  let v03 = cast U64 4 (vec_interleave_high (cast U128 2 o3) (cast U128 2 o3)) in
  let v13 = vec_add_mod o3 v03 in
  let v23 = vec_add_mod v13 (vec_permute4 v13 1ul 1ul 1ul 1ul) in
  lemma_fmul_r4_normalize51 #1 o3;

  let v04 = cast U64 4 (vec_interleave_high (cast U128 2 o4) (cast U128 2 o4)) in
  let v14 = vec_add_mod o4 v04 in
  let v24 = vec_add_mod v14 (vec_permute4 v14 1ul 1ul 1ul 1ul) in
  lemma_fmul_r4_normalize51 #1 o4;
  let res = (v20, v21, v22, v23, v24) in
  lemma_fmul_r4_normalize51_expand res fa;
  res

val fmul_r4_normalize5_lemma:
    acc:felem5 4
  -> r:felem5 4
  -> r_5:felem5 4
  -> r4:felem5 4
  -> Lemma
    (requires
      felem_fits5 acc (2, 3, 2, 2, 2) /\
      felem_fits5 r (1, 1, 1, 1, 1) /\
      felem_fits5 r4 (1, 2, 1, 1, 1) /\
      r_5 == precomp_r5 r /\
      feval5 r4 == S.compute_r4 (feval5 r))
    (ensures (
      let out = fmul_r4_normalize5 acc r r_5 r4 in
      acc_inv_t out /\
      (feval5 out).[0] == S.normalize_4 (feval5 acc) (feval5 r)))
  [SMTPat (fmul_r4_normalize5 acc r r_5 r4)]
let fmul_r4_normalize5_lemma acc fr fr_5 fr4 =
  let fr2 = fmul_r5 fr fr fr_5 in
  let fr3 = fmul_r5 fr2 fr fr_5 in
  let out = fmul_r4_normalize50 acc fr fr2 fr3 fr4 in
  let v2 = fmul_r4_normalize51 out in
  let res = carry_full_felem5 v2 in
  carry_full_felem5_lemma v2

val load_felem5_lemma:
    #w:lanes
  -> lo:uint64xN w
  -> hi:uint64xN w
  -> Lemma
    (let f = load_felem5 #w lo hi in
    felem_fits5 f (1, 1, 1, 1, 1) /\
    felem_less5 f (pow2 128) /\
    feval5 f == createi #S.pfelem w
      (fun i -> (uint64xN_v hi).[i] * pow2 64 + (uint64xN_v lo).[i]))
let load_felem5_lemma #w lo hi =
  let f = load_felem5 #w lo hi in
  let res = createi #S.pfelem w (fun i -> (uint64xN_v hi).[i] * pow2 64 + (uint64xN_v lo).[i]) in

  match w with
  | 1 ->
    load_felem5_lemma_i #w lo hi 0;
    eq_intro (feval5 f) res
  | 2 ->
    load_felem5_lemma_i #w lo hi 0;
    load_felem5_lemma_i #w lo hi 1;
    eq_intro (feval5 f) res
  | 4 ->
    load_felem5_lemma_i #w lo hi 0;
    load_felem5_lemma_i #w lo hi 1;
    load_felem5_lemma_i #w lo hi 2;
    load_felem5_lemma_i #w lo hi 3;
    eq_intro (feval5 f) res

val store_felem5_lemma:
    #w:lanes
  -> f:felem5 w
  -> Lemma
    (requires felem_fits5 f (1, 1, 1, 1, 1))
    (ensures
      (let (lo, hi) = store_felem5 f in
      (forall (i:nat). i < w ==>
	(uint64xN_v hi).[i] * pow2 64 + (uint64xN_v lo).[i] == (fas_nat5 f).[i] % pow2 128)))
    [SMTPat (store_felem5 f)]
let store_felem5_lemma #w f =
  match w with
  | 1 ->
    store_felem5_lemma_i #w f 0
  | 2 ->
    store_felem5_lemma_i #w f 0;
    store_felem5_lemma_i #w f 1
  | 4 ->
    store_felem5_lemma_i #w f 0;
    store_felem5_lemma_i #w f 1;
    store_felem5_lemma_i #w f 2;
    store_felem5_lemma_i #w f 3

val set_bit5_lemma:
  #w:lanes
  -> f:lseq (uint64xN w) 5
  -> i:size_nat{i <= 128}
  -> Lemma
    (requires
      lfelem_fits f (1, 1, 1, 1, 1) /\
      lfelem_less f (pow2 i))
    (ensures
      lfelem_fits (set_bit5 f i) (1, 1, 1, 1, 1) /\
      lfeval (set_bit5 f i) == map (S.pfadd (pow2 i)) (lfeval f))
let set_bit5_lemma #w f i =
  let tmp = map (S.pfadd (pow2 i)) (lfeval f) in
  match w with
  | 1 ->
    set_bit5_lemma_k #w f i 0;
    eq_intro (lfeval (set_bit5 f i)) tmp
  | 2 ->
    set_bit5_lemma_k #w f i 0;
    set_bit5_lemma_k #w f i 1;
    eq_intro (lfeval (set_bit5 f i)) tmp
  | 4 ->
    set_bit5_lemma_k #w f i 0;
    set_bit5_lemma_k #w f i 1;
    set_bit5_lemma_k #w f i 2;
    set_bit5_lemma_k #w f i 3;
    eq_intro (lfeval (set_bit5 f i)) tmp

val mod_add128_lemma:
    #w:lanes
  -> a:(uint64xN w & uint64xN w)
  -> b:(uint64xN w & uint64xN w)
  -> Lemma
    (let (r0, r1) = mod_add128_ws a b in
     let (a0, a1) = a in
     let (b0, b1) = b in
    (forall (i:nat). i < w ==>
    (uint64xN_v r1).[i] * pow2 64 + (uint64xN_v r0).[i] ==
      (((uint64xN_v a1).[i] + (uint64xN_v b1).[i]) * pow2 64 +
      (uint64xN_v a0).[i] + (uint64xN_v b0).[i]) % pow2 128))
let mod_add128_lemma #w a b =
  match w with
  | 1 ->
    mod_add128_lemma_i a b 0
  | 2 ->
    mod_add128_lemma_i a b 0;
    mod_add128_lemma_i a b 1
  | 4 ->
    mod_add128_lemma_i a b 0;
    mod_add128_lemma_i a b 1;
    mod_add128_lemma_i a b 2;
    mod_add128_lemma_i a b 3
