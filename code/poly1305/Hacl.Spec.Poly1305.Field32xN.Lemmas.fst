module Hacl.Spec.Poly1305.Field32xN.Lemmas

open Lib.IntTypes
open Lib.IntVector
open Lib.Sequence
open FStar.Mul

open Hacl.Spec.Poly1305.Field32xN
open Hacl.Poly1305.Field32xN.Lemmas0
open Hacl.Poly1305.Field32xN.Lemmas1
open Hacl.Poly1305.Field32xN.Lemmas2

module Vec = Hacl.Spec.Poly1305.Vec

#set-options "--z3rlimit 100 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"


val lemma_feval_is_fas_nat_i:
  #w:lanes
  -> f:felem5 w{felem_less5 f (pow2 128)}
  -> i:size_nat{i < w} ->
  Lemma ((feval5 f).[i] == (fas_nat5 f).[i])

let lemma_feval_is_fas_nat_i #w f i =
  assert_norm (pow2 128 < Vec.prime);
  assert ((feval5 f).[i] == (as_nat5 (transpose f).[i]) % Vec.prime);
  FStar.Math.Lemmas.modulo_lemma (as_nat5 (transpose f).[i]) Vec.prime

val lemma_feval_is_fas_nat:
    #w:lanes
  -> f:felem5 w{felem_less5 f (pow2 128)} ->
  Lemma (forall (i:nat). i < w ==> (fas_nat5 f).[i] == (feval5 f).[i])

let lemma_feval_is_fas_nat #w f =
  FStar.Classical.forall_intro (lemma_feval_is_fas_nat_i #w f)


val precomp_r5_fits_lemma:
    #w:lanes
  -> r:felem5 w{felem_fits5 r (1, 1, 1, 1, 1)} ->
  Lemma (felem_fits5 (precomp_r5 #w r) (5, 5, 5, 5, 5))
  [SMTPat (precomp_r5 #w r)]

let precomp_r5_fits_lemma #w r =
  FStar.Classical.forall_intro (precomp_r5_as_tup64 #w r)


val precomp_r5_fits_lemma2:
    #w:lanes
  -> r:felem5 w{felem_fits5 r (2, 2, 2, 2, 2)} ->
  Lemma (felem_fits5 (precomp_r5 #w r) (10, 10, 10, 10, 10))
  [SMTPat (precomp_r5 #w r)]

let precomp_r5_fits_lemma2 #w r =
  FStar.Classical.forall_intro (precomp_r5_as_tup64 #w r)


val fadd5_fits_lemma:
    #w:lanes
  -> f1:felem5 w{felem_fits5 f1 (2,2,2,2,2)}
  -> f2:felem5 w{felem_fits5 f2 (1,1,1,1,1)} ->
  Lemma (felem_fits5 (fadd5 f1 f2) (3,3,3,3,3))
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
  -> f1:felem5 w{felem_fits5 f1 (2,2,2,2,2)}
  -> f2:felem5 w{felem_fits5 f2 (1,1,1,1,1)} ->
  Lemma (feval5 (fadd5 f1 f2) == map2 Vec.pfadd (feval5 f1) (feval5 f2))
  [SMTPat (fadd5 f1 f2)]

let fadd5_eval_lemma #w f1 f2 =
  let o = fadd5 f1 f2 in
  FStar.Classical.forall_intro (fadd5_eval_lemma_i f1 f2);
  eq_intro (feval5 o) (map2 Vec.pfadd (feval5 f1) (feval5 f2))


val mul_felem5_fits_lemma:
    #w:lanes
  -> f1:felem5 w{felem_fits5 f1 (3, 3, 3, 3, 3)}
  -> r:felem5 w{felem_fits5 r (2, 2, 2, 2, 2)}
  -> r5:felem5 w{felem_fits5 r5 (10, 10, 10, 10, 10)} ->
  Lemma (felem_wide_fits5 (mul_felem5 #w f1 r r5) (126, 102, 78, 54, 30))
  [SMTPat (mul_felem5 #w f1 r r5)]

let mul_felem5_fits_lemma #w f1 r r5 =
  let (r0, r1, r2, r3, r4) = r in
  let (f10, f11, f12, f13, f14) = f1 in
  let (r50, r51, r52, r53, r54) = r5 in

  let (a0,a1,a2,a3,a4) = smul_felem5 #w f10 (r0,r1,r2,r3,r4) in
  smul_felem5_fits_lemma #w #3 #(2,2,2,2,2) f10 (r0,r1,r2,r3,r4);
  let (a10,a11,a12,a13,a14) = smul_add_felem5 #w f11 (r54,r0,r1,r2,r3) (a0,a1,a2,a3,a4) in
  smul_add_felem5_fits_lemma #w #3 #(10,2,2,2,2) #(6,6,6,6,6) f11 (r54,r0,r1,r2,r3) (a0,a1,a2,a3,a4);
  let (a20,a21,a22,a23,a24) = smul_add_felem5 #w f12 (r53,r54,r0,r1,r2) (a10,a11,a12,a13,a14) in
  smul_add_felem5_fits_lemma #w #3 #(10,10,2,2,2) #(36,12,12,12,12) f12 (r53,r54,r0,r1,r2) (a10,a11,a12,a13,a14);
  let (a30,a31,a32,a33,a34) = smul_add_felem5 #w f13 (r52,r53,r54,r0,r1) (a20,a21,a22,a23,a24) in
  smul_add_felem5_fits_lemma #w #3 #(10,10,10,2,2) #(66,42,18,18,18) f13 (r52,r53,r54,r0,r1) (a20,a21,a22,a23,a24);
  let (a40,a41,a42,a43,a44) = smul_add_felem5 #w f14 (r51,r52,r53,r54,r0) (a30,a31,a32,a33,a34) in
  smul_add_felem5_fits_lemma #w #3 #(10,10,10,10,2) #(96,72,48,24,24) f14 (r51,r52,r53,r54,r0) (a30,a31,a32,a33,a34)


val mul_felem5_eval_lemma_i:
    #w:lanes
  -> f1:felem5 w{felem_fits5 f1 (3, 3, 3, 3, 3)}
  -> r:felem5 w{felem_fits5 r (2, 2, 2, 2, 2)}
  -> r5:felem5 w{felem_fits5 r5 (10, 10, 10, 10, 10) /\ r5 == precomp_r5 r}
  -> i:nat{i < w} ->
  Lemma ((feval5 (mul_felem5 #w f1 r r5)).[i] == (feval5 f1).[i] `Vec.pfmul` (feval5 r).[i])

let mul_felem5_eval_lemma_i #w f1 r r5 i =
  let (r0, r1, r2, r3, r4) = r in
  let (f10, f11, f12, f13, f14) = f1 in
  let (r50, r51, r52, r53, r54) = r5 in

  let (a0,a1,a2,a3,a4) = smul_felem5 #w f10 (r0,r1,r2,r3,r4) in
  smul_felem5_eval_lemma #w #3 #(2,2,2,2,2) f10 (r0,r1,r2,r3,r4);
  smul_felem5_fits_lemma #w #3 #(2,2,2,2,2) f10 (r0,r1,r2,r3,r4);
  assert ((fas_nat5 (a0,a1,a2,a3,a4)).[i] == (uint64xN_v f10).[i] * (fas_nat5 (r0,r1,r2,r3,r4)).[i]);
  let (a10,a11,a12,a13,a14) = smul_add_felem5 #w f11 (r54,r0,r1,r2,r3) (a0,a1,a2,a3,a4) in
  smul_add_felem5_eval_lemma #w #3 #(10,2,2,2,2) #(6,6,6,6,6) f11 (r54,r0,r1,r2,r3) (a0,a1,a2,a3,a4);
  smul_add_felem5_fits_lemma #w #3 #(10,2,2,2,2) #(6,6,6,6,6) f11 (r54,r0,r1,r2,r3) (a0,a1,a2,a3,a4);
  assert ((fas_nat5 (a10,a11,a12,a13,a14)).[i] == (fas_nat5 (a0,a1,a2,a3,a4)).[i] + (uint64xN_v f11).[i] * (fas_nat5 (r54,r0,r1,r2,r3)).[i]);
  let (a20,a21,a22,a23,a24) = smul_add_felem5 #w f12 (r53,r54,r0,r1,r2) (a10,a11,a12,a13,a14) in
  smul_add_felem5_eval_lemma #w #3 #(10,10,2,2,2) #(36,12,12,12,12) f12 (r53,r54,r0,r1,r2) (a10,a11,a12,a13,a14);
  smul_add_felem5_fits_lemma #w #3 #(10,10,2,2,2) #(36,12,12,12,12) f12 (r53,r54,r0,r1,r2) (a10,a11,a12,a13,a14);
  assert ((fas_nat5 (a20,a21,a22,a23,a24)).[i] == (fas_nat5 (a10,a11,a12,a13,a14)).[i] + (uint64xN_v f12).[i] * (fas_nat5 (r53,r54,r0,r1,r2)).[i]);
  let (a30,a31,a32,a33,a34) = smul_add_felem5 #w f13 (r52,r53,r54,r0,r1) (a20,a21,a22,a23,a24) in
  smul_add_felem5_eval_lemma #w #3 #(10,10,10,2,2) #(66,42,18,18,18) f13 (r52,r53,r54,r0,r1) (a20,a21,a22,a23,a24);
  smul_add_felem5_fits_lemma #w #3 #(10,10,10,2,2) #(66,42,18,18,18) f13 (r52,r53,r54,r0,r1) (a20,a21,a22,a23,a24);
  assert ((fas_nat5 (a30,a31,a32,a33,a34)).[i] == (fas_nat5 (a20,a21,a22,a23,a24)).[i] + (uint64xN_v f13).[i] * (fas_nat5 (r52,r53,r54,r0,r1)).[i]);
  let (a40,a41,a42,a43,a44) = smul_add_felem5 #w f14 (r51,r52,r53,r54,r0) (a30,a31,a32,a33,a34) in
  smul_add_felem5_eval_lemma #w #3 #(10,10,10,10,2) #(96,72,48,24,24) f14 (r51,r52,r53,r54,r0) (a30,a31,a32,a33,a34);
  smul_add_felem5_fits_lemma #w #3 #(10,10,10,10,2) #(96,72,48,24,24) f14 (r51,r52,r53,r54,r0) (a30,a31,a32,a33,a34);
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
  -> f1:felem5 w{felem_fits5 f1 (3, 3, 3, 3, 3)}
  -> r:felem5 w{felem_fits5 r (2, 2, 2, 2, 2)}
  -> r5:felem5 w{felem_fits5 r5 (10, 10, 10, 10, 10) /\ r5 == precomp_r5 r} ->
  Lemma (feval5 (mul_felem5 #w f1 r r5) == map2 (Vec.pfmul) (feval5 f1) (feval5 r))
  [SMTPat (mul_felem5 #w f1 r r5)]

let mul_felem5_eval_lemma #w f1 r r5 =
  let tmp = map2 (Vec.pfmul) (feval5 f1) (feval5 r) in
  FStar.Classical.forall_intro (mul_felem5_eval_lemma_i #w f1 r r5);
  eq_intro (feval5 (mul_felem5 #w f1 r r5)) tmp


val fmul_r5_fits_lemma:
    #w:lanes
  -> f1:felem5 w{felem_fits5 f1 (3, 3, 3, 3, 3)}
  -> r:felem5 w{felem_fits5 r (2, 2, 2, 2, 2)}
  -> r5:felem5 w{felem_fits5 r5 (10, 10, 10, 10, 10)} ->
  Lemma (felem_fits5 (fmul_r5 #w f1 r r5) (1, 2, 1, 1, 2))
  [SMTPat (fmul_r5 #w f1 r r5)]

let fmul_r5_fits_lemma #w f1 r r5 =
  let tmp = mul_felem5 f1 r r5 in
  mul_felem5_fits_lemma #w f1 r r5;
  let res = carry_wide_felem5 tmp in
  carry_wide_felem5_fits_lemma #w tmp


val fmul_r5_eval_lemma:
    #w:lanes
  -> f1:felem5 w{felem_fits5 f1 (3, 3, 3, 3, 3)}
  -> r:felem5 w{felem_fits5 r (2, 2, 2, 2, 2)}
  -> r5:felem5 w{felem_fits5 r5 (10, 10, 10, 10, 10) /\ r5 == precomp_r5 r} ->
  Lemma (feval5 (fmul_r5 #w f1 r r5) == map2 (Vec.pfmul) (feval5 f1) (feval5 r))
  [SMTPat (fmul_r5 #w f1 r r5)]

let fmul_r5_eval_lemma #w f1 r r5 =
  let tmp = mul_felem5 f1 r r5 in
  mul_felem5_eval_lemma #w f1 r r5;
  let res = carry_wide_felem5 tmp in
  carry_wide_felem5_eval_lemma #w tmp


val fadd_mul_r5_fits_lemma:
    #w:lanes
  -> acc:felem5 w{felem_fits5 acc (2, 2, 2, 2, 2)}
  -> f1:felem5 w{felem_fits5 f1 (1, 1, 1, 1, 1)}
  -> r:felem5 w{felem_fits5 r (1, 1, 1, 1, 1)}
  -> r5:felem5 w{felem_fits5 r5 (5, 5, 5, 5, 5)} ->
  Lemma (felem_fits5 (fadd_mul_r5 acc f1 r r5) (1, 2, 1, 1, 2))
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
  -> acc:felem5 w{felem_fits5 acc (2, 2, 2, 2, 2)}
  -> f1:felem5 w{felem_fits5 f1 (1, 1, 1, 1, 1)}
  -> r:felem5 w{felem_fits5 r (1, 1, 1, 1, 1)}
  -> r5:felem5 w{felem_fits5 r5 (5, 5, 5, 5, 5) /\ r5 == precomp_r5 r} ->
  Lemma (feval5 (fadd_mul_r5 acc f1 r r5) ==
    map2 (Vec.pfmul) (map2 (Vec.pfadd) (feval5 acc) (feval5 f1)) (feval5 r))
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
  -> f:felem5 w{felem_fits5 f (2, 2, 2, 2, 2)} ->
  Lemma
  (felem_fits5 (reduce_felem5 f) (1, 1, 1, 1, 1) /\
   (feval5 f).[0] == (fas_nat5 (reduce_felem5 f)).[0])
  [SMTPat (reduce_felem5 f)]

let reduce_felem5_eval_lemma #w f =
  carry_full_felem5_eval_lemma f;
  carry_full_felem5_fits_lemma f;
  let f = carry_full_felem5 f in
  carry_reduce_felem5_lemma #w f;
  subtract_p5_felem5_lemma #w (carry_full_felem5 f)


val fmul_r2_normalize50:
    acc:felem5 2
  -> r:felem5 2
  -> r2:felem5 2 ->
  Pure (felem5 2)
  (requires
    felem_fits5 acc (3, 3, 3, 3, 3) /\
    felem_fits5 r (1, 1, 1, 1, 1) /\
    felem_fits5 r2 (2, 2, 2, 2, 2) /\
    feval5 r2 == Vec.compute_r2 (feval5 r).[0])
  (ensures fun a ->
    let fr21 = create2 (feval5 r2).[0] (feval5 r).[0] in
    feval5 a == Vec.fmul (feval5 acc) fr21 /\
    felem_fits5 a (1, 2, 1, 1, 2))

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
  assert ((feval5 fr2).[0] == Vec.pfmul ((feval5 fr).[0]) ((feval5 fr).[0]));

  let fr21 = (r210, r211, r212, r213, r214) in
  eq_intro (feval5 fr21) (create2 (feval5 fr2).[0] (feval5 fr).[0]);
  assert (feval5 fr21 == create2 (feval5 fr2).[0] (feval5 fr).[0]);

  assert (felem_fits5 fr21 (2, 2, 2, 2, 2));
  let fr215 = precomp_r5 #2 fr21 in
  let a = fmul_r5 #2 acc fr21 fr215 in
  fmul_r5_eval_lemma acc fr21 fr215;
  fmul_r5_fits_lemma acc fr21 fr215;
  assert (feval5 a == Vec.fmul (feval5 acc) (feval5 fr21));
  assert (felem_fits5 a (1, 2, 1, 1, 2));
  a


#push-options "--z3rlimit 150"
val fmul_r2_normalize51:
    a:felem5 2
  -> fa1:felem5 2 ->
  Pure (felem5 2)
  (requires
    felem_fits5 a (1, 2, 1, 1, 2) /\
    felem_fits5 fa1 (1, 2, 1, 1, 2) /\
    feval5 fa1 == create2 (feval5 a).[1] (feval5 a).[1])
  (ensures fun out ->
    (feval5 out).[0] == Vec.pfadd (feval5 a).[0] (feval5 a).[1] /\
    felem_fits5 out (2, 4, 2, 2, 4))

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
  assert (felem_fits5 out (2, 4, 2, 2, 4));

  calc (==) {
    ((feval5 a).[0] + (feval5 a).[1]) % Vec.prime;
    (==) { }
    (as_nat5 (a0, a1, a2, a3, a4) % Vec.prime + as_nat5 (a10, a11, a12, a13, a14) % Vec.prime) % Vec.prime;
    (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_l
    (as_nat5 (a0, a1, a2, a3, a4)) (as_nat5 (a10, a11, a12, a13, a14)) Vec.prime;
  FStar.Math.Lemmas.lemma_mod_plus_distr_r
    (as_nat5 (a0, a1, a2, a3, a4) % Vec.prime) (as_nat5 (a10, a11, a12, a13, a14)) Vec.prime }
    (as_nat5 (a0, a1, a2, a3, a4) + as_nat5 (a10, a11, a12, a13, a14)) % Vec.prime;
    (==) { }
    (feval5 out).[0];
  };
  out
#pop-options


val fmul_r2_normalize5_lemma:
    acc:felem5 2
  -> r:felem5 2
  -> r2:felem5 2 ->
  Lemma
  (requires
    felem_fits5 acc (3, 3, 3, 3, 3) /\
    felem_fits5 r (1, 1, 1, 1, 1) /\
    felem_fits5 r2 (2, 2, 2, 2, 2) /\
    feval5 r2 == Vec.compute_r2 (feval5 r).[0])
  (ensures
    (let out = fmul_r2_normalize5 acc r r2 in
    felem_fits5 out (2, 1, 1, 1, 1) /\
    (feval5 out).[0] == Vec.normalize_2 (feval5 r).[0] (feval5 acc)))
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
  assert (felem_fits5 fa1 (1, 2, 1, 1, 2));

  let out = fmul_r2_normalize51 a fa1 in
  assert ((feval5 out).[0] == Vec.pfadd (feval5 a).[0] (feval5 a).[1]);

  let res = carry_full_felem5 out in
  carry_full_felem5_lemma out


val fmul_r4_normalize50:
    acc:felem5 4
  -> r:felem5 4
  -> r2:felem5 4
  -> r3:felem5 4
  -> r4:felem5 4 ->
  Pure (felem5 4)
  (requires
    felem_fits5 acc (3, 3, 3, 3, 3) /\
    felem_fits5 r (1, 1, 1, 1, 1) /\
    felem_fits5 r2 (2, 2, 2, 2, 2) /\
    felem_fits5 r3 (2, 2, 2, 2, 2) /\
    felem_fits5 r4 (2, 2, 2, 2, 2) /\
    feval5 r2 == Vec.fmul (feval5 r) (feval5 r) /\
    feval5 r3 == Vec.fmul (feval5 r2) (feval5 r) /\
    feval5 r4 == Vec.compute_r4 (feval5 r).[0])
  (ensures fun out ->
    let fr4321 = create4 (feval5 r4).[0] (feval5 r3).[0] (feval5 r2).[0] (feval5 r).[0] in
    feval5 out == Vec.fmul (feval5 acc) fr4321 /\
    felem_fits5 out (1, 2, 1, 1, 2))

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
  let r12340 = vec_interleave_low_n 2 v34340 v12120 in
  vec_interleave_low_n_lemma_uint64_4_2 v34340 v12120;

  let v12121 = vec_interleave_low r21 r11 in
  vec_interleave_low_lemma_uint64_4 r21 r11;
  let v34341 = vec_interleave_low r41 r31 in
  vec_interleave_low_lemma_uint64_4 r41 r31;
  let r12341 = vec_interleave_low_n 2 v34341 v12121 in
  vec_interleave_low_n_lemma_uint64_4_2 v34341 v12121;

  let v12122 = vec_interleave_low r22 r12 in
  vec_interleave_low_lemma_uint64_4 r22 r12;
  let v34342 = vec_interleave_low r42 r32 in
  vec_interleave_low_lemma_uint64_4 r42 r32;
  let r12342 = vec_interleave_low_n 2 v34342 v12122 in
  vec_interleave_low_n_lemma_uint64_4_2 v34342 v12122;

  let v12123 = vec_interleave_low r23 r13 in
  vec_interleave_low_lemma_uint64_4 r23 r13;
  let v34343 = vec_interleave_low r43 r33 in
  vec_interleave_low_lemma_uint64_4 r43 r33;
  let r12343 = vec_interleave_low_n 2 v34343 v12123 in
  vec_interleave_low_n_lemma_uint64_4_2 v34343 v12123;

  let v12124 = vec_interleave_low r24 r14 in
  vec_interleave_low_lemma_uint64_4 r24 r14;
  let v34344 = vec_interleave_low r44 r34 in
  vec_interleave_low_lemma_uint64_4 r44 r34;
  let r12344 = vec_interleave_low_n 2 v34344 v12124 in
  vec_interleave_low_n_lemma_uint64_4_2 v34344 v12124;

  let fr1234 = (r12340, r12341, r12342, r12343, r12344) in
  eq_intro (feval5 fr1234) (create4 (feval5 fr4).[0] (feval5 fr3).[0] (feval5 fr2).[0] (feval5 fr).[0]);

  let fr12345 = precomp_r5 #4 fr1234 in
  let out = fmul_r5 #4 acc fr1234 fr12345 in
  fmul_r5_eval_lemma acc fr1234 fr12345;
  fmul_r5_fits_lemma acc fr1234 fr12345;
  out


val lemma_fmul_r4_normalize51:
    #m:scale32{m <= 2}
  -> o:uint64xN 4{felem_fits1 o m} ->
  Lemma
  (let v00 = vec_interleave_high_n 2 o o in
   let v10 = vec_add_mod o v00 in
   let v20 = vec_add_mod v10 (vec_permute4 v10 1ul 1ul 1ul 1ul) in
   felem_fits1 v20 (4 * m) /\
   (uint64xN_v v20).[0] == (uint64xN_v o).[0] + (uint64xN_v o).[1] + (uint64xN_v o).[2] + (uint64xN_v o).[3])

let lemma_fmul_r4_normalize51 #m o =
  let v00 = vec_interleave_high_n 2 o o in
  vec_interleave_high_n_lemma_uint64_4_2 o o;
  let (o0, o1, o2, o3) = ((vec_v o).[0], (vec_v o).[1], (vec_v o).[2], (vec_v o).[3]) in
  assert (vec_v v00 == create4 o2 o3 o2 o3);
  let v10 = vec_add_mod o v00 in
  FStar.Math.Lemmas.modulo_lemma (v o0 + v o2) (pow2 64);
  FStar.Math.Lemmas.modulo_lemma (v o1 + v o3) (pow2 64);
  assert (v (vec_v v10).[0] == v o0 + v o2);
  assert (v (vec_v v10).[1] == v o1 + v o3);
  let v20 = vec_add_mod v10 (vec_permute4 v10 1ul 1ul 1ul 1ul) in
  FStar.Math.Lemmas.modulo_lemma (v o0 + v o2 + v o1 + v o3) (pow2 64)


val lemma_fmul_r4_normalize51_expand:
    v2:felem5 4
  -> out:felem5 4 ->
  Lemma
  (requires
   (let (v20, v21, v22, v23, v24) = v2 in
    let (o0, o1, o2, o3, o4) = out in
    (uint64xN_v v20).[0] == (uint64xN_v o0).[0] + (uint64xN_v o0).[1] + (uint64xN_v o0).[2] + (uint64xN_v o0).[3] /\
    (uint64xN_v v21).[0] == (uint64xN_v o1).[0] + (uint64xN_v o1).[1] + (uint64xN_v o1).[2] + (uint64xN_v o1).[3] /\
    (uint64xN_v v22).[0] == (uint64xN_v o2).[0] + (uint64xN_v o2).[1] + (uint64xN_v o2).[2] + (uint64xN_v o2).[3] /\
    (uint64xN_v v23).[0] == (uint64xN_v o3).[0] + (uint64xN_v o3).[1] + (uint64xN_v o3).[2] + (uint64xN_v o3).[3] /\
    (uint64xN_v v24).[0] == (uint64xN_v o4).[0] + (uint64xN_v o4).[1] + (uint64xN_v o4).[2] + (uint64xN_v o4).[3]))
  (ensures
    (let (v20, v21, v22, v23, v24) = v2 in
     let (o0, o1, o2, o3, o4) = out in
     (feval5 v2).[0] == Vec.pfadd (Vec.pfadd (Vec.pfadd (feval5 out).[0] (feval5 out).[1]) (feval5 out).[2]) (feval5 out).[3]))

let lemma_fmul_r4_normalize51_expand v2 out =
  let (v20, v21, v22, v23, v24) = as_tup64_i v2 0 in
  let (o0, o1, o2, o3, o4) = out in

  calc (==) {
    as_nat5 (v20, v21, v22, v23, v24) % Vec.prime;
    (==) { }
    (as_nat5 (as_tup64_i out 0) + as_nat5 (as_tup64_i out 1) + as_nat5 (as_tup64_i out 2) + as_nat5 (as_tup64_i out 3)) % Vec.prime;
    (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_l (as_nat5 (as_tup64_i out 0) + as_nat5 (as_tup64_i out 1))
	 (as_nat5 (as_tup64_i out 2) + as_nat5 (as_tup64_i out 3)) Vec.prime }
    ((as_nat5 (as_tup64_i out 0) + as_nat5 (as_tup64_i out 1)) % Vec.prime + as_nat5 (as_tup64_i out 2) + as_nat5 (as_tup64_i out 3)) % Vec.prime;
    (==) { FStar.Math.Lemmas.modulo_distributivity (as_nat5 (as_tup64_i out 0)) (as_nat5 (as_tup64_i out 1)) Vec.prime }
    (((feval5 out).[0] + (feval5 out).[1]) % Vec.prime + as_nat5 (as_tup64_i out 2) + as_nat5 (as_tup64_i out 3)) % Vec.prime;
    (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_l (((feval5 out).[0] + (feval5 out).[1]) % Vec.prime + as_nat5 (as_tup64_i out 2))
	(as_nat5 (as_tup64_i out 3)) Vec.prime }
    ((((feval5 out).[0] + (feval5 out).[1]) % Vec.prime + as_nat5 (as_tup64_i out 2)) % Vec.prime + as_nat5 (as_tup64_i out 3)) % Vec.prime;
    (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_r (((feval5 out).[0] + (feval5 out).[1]) % Vec.prime) (as_nat5 (as_tup64_i out 2)) Vec.prime }
    ((((feval5 out).[0] + (feval5 out).[1]) % Vec.prime + (feval5 out).[2]) % Vec.prime + as_nat5 (as_tup64_i out 3)) % Vec.prime;
    (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_r ((((feval5 out).[0] + (feval5 out).[1]) % Vec.prime + (feval5 out).[2]) % Vec.prime)
	 (as_nat5 (as_tup64_i out 3)) Vec.prime }
    ((((feval5 out).[0] + (feval5 out).[1]) % Vec.prime + (feval5 out).[2]) % Vec.prime + (feval5 out).[3]) % Vec.prime;
   };
  assert ((feval5 v2).[0] ==
    ((((feval5 out).[0] + (feval5 out).[1]) % Vec.prime + (feval5 out).[2]) % Vec.prime + (feval5 out).[3]) % Vec.prime)


val fmul_r4_normalize51: a:felem5 4 ->
  Pure (felem5 4)
  (requires felem_fits5 a (1, 2, 1, 1, 2))
  (ensures  fun res ->
    felem_fits5 res (4, 8, 4, 4, 8) /\
    (feval5 res).[0] == Vec.pfadd (Vec.pfadd (Vec.pfadd (feval5 a).[0] (feval5 a).[1]) (feval5 a).[2]) (feval5 a).[3])

let fmul_r4_normalize51 fa =
  let (o0, o1, o2, o3, o4) = fa in
  let v00 = vec_interleave_high_n 2 o0 o0 in
  let v10 = vec_add_mod o0 v00 in
  let v20 = vec_add_mod v10 (vec_permute4 v10 1ul 1ul 1ul 1ul) in
  lemma_fmul_r4_normalize51 #1 o0;

  let v01 = vec_interleave_high_n 2 o1 o1 in
  let v11 = vec_add_mod o1 v01 in
  let v21 = vec_add_mod v11 (vec_permute4 v11 1ul 1ul 1ul 1ul) in
  lemma_fmul_r4_normalize51 #2 o1;

  let v02 = vec_interleave_high_n 2 o2 o2 in
  let v12 = vec_add_mod o2 v02 in
  let v22 = vec_add_mod v12 (vec_permute4 v12 1ul 1ul 1ul 1ul) in
  lemma_fmul_r4_normalize51 #1 o2;

  let v03 = vec_interleave_high_n 2 o3 o3 in
  let v13 = vec_add_mod o3 v03 in
  let v23 = vec_add_mod v13 (vec_permute4 v13 1ul 1ul 1ul 1ul) in
  lemma_fmul_r4_normalize51 #1 o3;

  let v04 = vec_interleave_high_n 2 o4 o4 in
  let v14 = vec_add_mod o4 v04 in
  let v24 = vec_add_mod v14 (vec_permute4 v14 1ul 1ul 1ul 1ul) in
  lemma_fmul_r4_normalize51 #2 o4;
  let res = (v20, v21, v22, v23, v24) in
  lemma_fmul_r4_normalize51_expand res fa;
  res


val fmul_r4_normalize5_lemma:
    acc:felem5 4
  -> r:felem5 4
  -> r_5:felem5 4
  -> r4:felem5 4 ->
  Lemma
  (requires
    felem_fits5 acc (3, 3, 3, 3, 3) /\
    felem_fits5 r (1, 1, 1, 1, 1) /\
    felem_fits5 r4 (2, 2, 2, 2, 2) /\
    r_5 == precomp_r5 r /\
    feval5 r4 == Vec.compute_r4 (feval5 r).[0])
  (ensures
    (let out = fmul_r4_normalize5 acc r r_5 r4 in
     felem_fits5 out (2, 1, 1, 1, 1) /\
    (feval5 out).[0] == Vec.normalize_4 (feval5 r).[0] (feval5 acc)))
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
  -> hi:uint64xN w ->
  Lemma
  (let f = load_felem5 #w lo hi in
   felem_fits5 f (1, 1, 1, 1, 1) /\
   felem_less5 f (pow2 128) /\
   feval5 f == createi #Vec.pfelem w
     (fun i -> (uint64xN_v hi).[i] * pow2 64 + (uint64xN_v lo).[i]))

let load_felem5_lemma #w lo hi =
  let f = load_felem5 #w lo hi in
  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 128 < Vec.prime);
  let res = createi #Vec.pfelem w
    (fun i -> (uint64xN_v hi).[i] * pow2 64 + (uint64xN_v lo).[i]) in

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

val load_felem5_4_interleave: lo:uint64xN 4 -> hi:uint64xN 4 -> Lemma
  (let m0 = vec_interleave_low_n 2 lo hi in
   let m1 = vec_interleave_high_n 2 lo hi in
   let m2 = cast U64 4 (vec_shift_right (cast U128 2 m0) 48ul) in
   let m3 = cast U64 4 (vec_shift_right (cast U128 2 m1) 48ul) in
   let m4 = vec_interleave_high m0 m1 in
   let t0 = vec_interleave_low m0 m1 in
   let t3 = vec_interleave_low m2 m3 in
   vec_v m4 == create4 (vec_v lo).[1] (vec_v lo).[3] (vec_v hi).[1] (vec_v hi).[3] /\
   vec_v t0 == create4 (vec_v lo).[0] (vec_v lo).[2] (vec_v hi).[0] (vec_v hi).[2] /\
   t3 == vec_or (vec_shift_right t0 48ul) (vec_shift_left m4 16ul))

let load_felem5_4_interleave lo hi =
  let m0 = vec_interleave_low_n 2 lo hi in
  vec_interleave_low_n_lemma_uint64_4_2 lo hi;
  //assert (vec_v m0 == create4 (vec_v lo).[0] (vec_v lo).[1] (vec_v hi).[0] (vec_v hi).[1]);
  let m1 = vec_interleave_high_n 2 lo hi in
  vec_interleave_high_n_lemma_uint64_4_2 lo hi;
  //assert (vec_v m1 == create4 (vec_v lo).[2] (vec_v lo).[3] (vec_v hi).[2] (vec_v hi).[3]);

  let m4 = vec_interleave_high m0 m1 in
  vec_interleave_high_lemma_uint64_4 m0 m1;
  //assert (vec_v m4 == create4 (vec_v m0).[1] (vec_v m1).[1] (vec_v m0).[3] (vec_v m1).[3]);
  assert (vec_v m4 == create4 (vec_v lo).[1] (vec_v lo).[3] (vec_v hi).[1] (vec_v hi).[3]);
  let t0 = vec_interleave_low m0 m1 in
  vec_interleave_low_lemma_uint64_4 m0 m1;
  //assert (vec_v t0 == create4 (vec_v m0).[0] (vec_v m1).[0] (vec_v m0).[2] (vec_v m1).[2]);
  assert (vec_v t0 == create4 (vec_v lo).[0] (vec_v lo).[2] (vec_v hi).[0] (vec_v hi).[2]);

  let m2 = cast U64 4 (vec_shift_right (cast U128 2 m0) 48ul) in
  vec_shift_right_uint128_small2 m0 48ul;
  assert ((vec_v m2).[0] == (((vec_v lo).[0] >>. 48ul) |. ((vec_v lo).[1] <<. 16ul)));
  assert ((vec_v m2).[2] == (((vec_v hi).[0] >>. 48ul) |. ((vec_v hi).[1] <<. 16ul)));
  let m3 = cast U64 4 (vec_shift_right (cast U128 2 m1) 48ul) in
  vec_shift_right_uint128_small2 m1 48ul;
  assert ((vec_v m3).[0] == (((vec_v lo).[2] >>. 48ul) |. ((vec_v lo).[3] <<. 16ul)));
  assert ((vec_v m3).[2] == (((vec_v hi).[2] >>. 48ul) |. ((vec_v hi).[3] <<. 16ul)));

  let t3 = vec_interleave_low m2 m3 in
  vec_interleave_low_lemma_uint64_4 m2 m3;
  eq_intro (vec_v t3) (vec_v (vec_or (vec_shift_right t0 48ul) (vec_shift_left m4 16ul)));
  vecv_extensionality t3 (vec_or (vec_shift_right t0 48ul) (vec_shift_left m4 16ul))

noextract
val load_felem5_4_compact: lo:uint64xN 4 -> hi:uint64xN 4 -> felem5 4
let load_felem5_4_compact lo hi =
  let mask26 = mask26 4 in
  let t3 = vec_or (vec_shift_right lo 48ul) (vec_shift_left hi 16ul) in
  let o0 = vec_and lo mask26 in
  let o1 = vec_and (vec_shift_right lo 26ul) mask26 in
  let o2 = vec_and (vec_shift_right t3 4ul) mask26 in
  let o3 = vec_and (vec_shift_right t3 30ul) mask26 in
  let o4 = vec_shift_right hi 40ul in
  (o0, o1, o2, o3, o4)

val load_felem5_4_compact_lemma_i: lo:uint64xN 4 -> hi:uint64xN 4 -> i:nat{i < 4} ->
  Lemma
  (let f = as_tup64_i (load_felem5_4_compact lo hi) i in
   tup64_fits5 f (1, 1, 1, 1, 1) /\
   as_nat5 f < pow2 128 /\
   as_nat5 f % Vec.prime == (uint64xN_v hi).[i] * pow2 64 + (uint64xN_v lo).[i])

let load_felem5_4_compact_lemma_i lo hi i =
  assert (as_tup64_i (load_felem5_4_compact lo hi) i == load_tup64_4_compact (vec_v lo).[i] (vec_v hi).[i]);
  load_tup64_4_compact_lemma (vec_v lo).[i] (vec_v hi).[i]


val load_felem5_4_lemma: lo:uint64xN 4 -> hi:uint64xN 4 ->
  Lemma
  (let f = load_felem5_4_compact lo hi in
   felem_fits5 f (1, 1, 1, 1, 1) /\
   felem_less5 f (pow2 128) /\
   feval5 f == createi #Vec.pfelem 4 (fun i -> (uint64xN_v hi).[i] * pow2 64 + (uint64xN_v lo).[i]))

let load_felem5_4_lemma lo hi =
  let f = load_felem5_4_compact lo hi in
  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 128 < Vec.prime);
  let res = createi #Vec.pfelem 4
    (fun i -> (uint64xN_v hi).[i] * pow2 64 + (uint64xN_v lo).[i]) in

  load_felem5_4_compact_lemma_i lo hi 0;
  load_felem5_4_compact_lemma_i lo hi 1;
  load_felem5_4_compact_lemma_i lo hi 2;
  load_felem5_4_compact_lemma_i lo hi 3;
  eq_intro (feval5 f) res

val load_felem5_le: b:lseq uint8 64 -> Lemma
  (let lo0 = vec_from_bytes_le U64 4 (sub b 0 32) in
   let hi0 = vec_from_bytes_le U64 4 (sub b 32 32) in
   let f = load_felem5_4 lo0 hi0 in
   felem_fits5 f (1, 1, 1, 1, 1) /\
   felem_less5 f (pow2 128) /\
   feval5 f == Vec.load_elem4 b)
let load_felem5_le b =
  let lo0 = vec_from_bytes_le U64 4 (sub b 0 32) in
  let hi0 = vec_from_bytes_le U64 4 (sub b 32 32) in
  let lo1 = vec_interleave_low_n 2 lo0 hi0 in
  let hi1 = vec_interleave_high_n 2 lo0 hi0 in

  let lo = vec_interleave_low lo1 hi1 in
  let hi = vec_interleave_high lo1 hi1 in

  let out = load_felem5_4_compact lo hi in
  load_felem5_4_interleave lo0 hi0;
  assert (out == load_felem5_4 lo0 hi0);
  load_felem5_4_lemma lo hi;
  Hacl.Impl.Poly1305.Lemmas.uints_from_bytes_le_lemma64_4 b;
  eq_intro (feval5 out) (Vec.load_elem4 b)


val load_acc5_2_lemma:
    f:felem5 2{felem_fits5 f (2, 2, 2, 2, 2)}
  -> e:felem5 2{felem_fits5 e (1, 1, 1, 1, 1)} ->
  Lemma
  (let res = load_acc5_2 f e in
   felem_fits5 res (3, 3, 3, 3, 3) /\
   feval5 res == Vec.fadd (create2 (feval5 f).[0] 0) (feval5 e))
  [SMTPat (load_acc5_2 f e)]

let load_acc5_2_lemma f e =
  let (f0, f1, f2, f3, f4) = f in
  let r0 = vec_set f0 1ul (u64 0) in
  let r1 = vec_set f1 1ul (u64 0) in
  let r2 = vec_set f2 1ul (u64 0) in
  let r3 = vec_set f3 1ul (u64 0) in
  let r4 = vec_set f4 1ul (u64 0) in
  let r = (r0, r1, r2, r3, r4) in
  //assert ((feval5 r).[0] == (feval5 f).[0]);
  assert ((feval5 r).[1] == 0);
  eq_intro (feval5 r) (create2 (feval5 f).[0] 0)


val load_acc5_4_lemma:
    f:felem5 4{felem_fits5 f (2, 2, 2, 2, 2)}
  -> e:felem5 4{felem_fits5 e (1, 1, 1, 1, 1)} ->
  Lemma
  (let res = load_acc5_4 f e in
   felem_fits5 res (3, 3, 3, 3, 3) /\
   feval5 res == Vec.fadd (create4 (feval5 f).[0] 0 0 0) (feval5 e))
  [SMTPat (load_acc5_4 f e)]

let load_acc5_4_lemma f e =
  let (f0, f1, f2, f3, f4) = f in
  let (r0, r1, r2, r3, r4) = (zero 4, zero 4, zero 4, zero 4, zero 4) in
  let r = (r0, r1, r2, r3, r4) in
  assert ((feval5 r).[1] == 0);
  assert ((feval5 r).[2] == 0);
  assert ((feval5 r).[3] == 0);
  let r0 = vec_set r0 0ul (vec_get f0 0ul) in
  let r1 = vec_set r1 0ul (vec_get f1 0ul) in
  let r2 = vec_set r2 0ul (vec_get f2 0ul) in
  let r3 = vec_set r3 0ul (vec_get f3 0ul) in
  let r4 = vec_set r4 0ul (vec_get f4 0ul) in
  let r = (r0, r1, r2, r3, r4) in
  assert ((feval5 r).[0] == (feval5 f).[0]);
  assert ((feval5 r).[1] == 0);
  assert ((feval5 r).[2] == 0);
  assert ((feval5 r).[3] == 0);
  eq_intro (feval5 r) (create4 (feval5 f).[0] 0 0 0)


val store_felem5_lemma:
    #w:lanes
  -> f:felem5 w{felem_fits5 f (1, 1, 1, 1, 1)} ->
  Lemma
  (let (lo, hi) = store_felem5 f in
   v hi * pow2 64 + v lo == (fas_nat5 f).[0] % pow2 128)
  [SMTPat (store_felem5 f)]

let store_felem5_lemma #w f =
  store_felem5_lemma #w f


val set_bit5_lemma:
    #w:lanes
  -> f:lseq (uint64xN w) 5
  -> i:size_nat{i <= 128} ->
  Lemma
  (requires
    lfelem_fits f (1, 1, 1, 1, 1) /\
    lfelem_less f (pow2 i))
  (ensures
    lfelem_fits (set_bit5 f i) (1, 1, 1, 1, 1) /\
    lfeval (set_bit5 f i) == map (Vec.pfadd (pow2 i)) (lfeval f))

let set_bit5_lemma #w f i =
  let tmp = map (Vec.pfadd (pow2 i)) (lfeval f) in
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

val add_mod_small: a:nat -> b:nat -> n:pos -> Lemma
  (requires a % n + b % n < n)
  (ensures  a % n + b % n == (a + b) % n)

let add_mod_small a b n =
  FStar.Math.Lemmas.modulo_lemma (a % n + b % n) n;
  assert (a % n + b % n == (a % n + b % n) % n);
  FStar.Math.Lemmas.lemma_mod_plus_distr_l a (b % n) n;
  FStar.Math.Lemmas.lemma_mod_plus_distr_r a b n

val mod_add128_lemma:
    a:(uint64 & uint64)
  -> b:(uint64 & uint64) ->
  Lemma
  (let (r0, r1) = mod_add128 a b in
   let (a0, a1) = a in let (b0, b1) = b in
   v r1 * pow2 64 + v r0 == ((v a1 + v b1) * pow2 64 + v a0 + v b0) % pow2 128)

let mod_add128_lemma a b =
  let (a0, a1) = a in
  let (b0, b1) = b in
  let r0 = a0 +. b0 in
  let r1 = a1 +. b1 in
  let c = r0 ^. ((r0 ^. b0) |. ((r0 -. b0) ^. b0)) >>. 63ul in
  // This is a well-documented assume that is also present in FStar's own
  // FStar.UInt128.fst. The lemma can be proven for 8-bit integers via Z3's
  // bitvector theory, as follows:
  //
  // open FStar.BV
  // let test (a b:bv_t 8) =
  // let ( ^ ) = bvxor in
  // let ( ||| ) = bvor in
  // let ( --- ) = bvsub in
  // let ( >> ) = bvshr in
  // assume (bvult a b);
  // assert (((a ^ ((a ^ b) ||| ((a --- b) ^ b))) >> 7) == (int2bv 1))
  //
  // Unfortunately, z3 times out for larger bit widths.
  assume (v c == (if v r0 < v b0 then 1 else 0));
  assert (v c == (v a0 + v b0) / pow2 64);
  let r2 = r1 +. c in

  calc (==) {
    v r2 * pow2 64 + v r0;
    (==) { }
    ((v a1 + v b1) % pow2 64 + (v a0 + v b0) / pow2 64) % pow2 64 * pow2 64 + (v a0 + v b0) % pow2 64;
    (==) { FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_2 ((v a1 + v b1) % pow2 64 + (v a0 + v b0) / pow2 64) 128 64 }
    ((v a1 + v b1) % pow2 64 + (v a0 + v b0) / pow2 64) * pow2 64 % pow2 128 + (v a0 + v b0) % pow2 64;
    (==) { }
    ((v a1 + v b1) % pow2 64 * pow2 64 + (v a0 + v b0) / pow2 64 * pow2 64) % pow2 128 + (v a0 + v b0) % pow2 64;
    (==) { FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v a1 + v b1) 128 64 }
    ((v a1 + v b1) * pow2 64 % pow2 128 + (v a0 + v b0) / pow2 64 * pow2 64) % pow2 128 + (v a0 + v b0) % pow2 64;
    (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_l ((v a1 + v b1) * pow2 64) ((v a0 + v b0) / pow2 64 * pow2 64) (pow2 128) }
    ((v a1 + v b1) * pow2 64 + (v a0 + v b0) / pow2 64 * pow2 64) % pow2 128 + (v a0 + v b0) % pow2 64;
    (==) { FStar.Math.Lemmas.modulo_lemma ((v a0 + v b0) % pow2 64) (pow2 128) }
    ((v a1 + v b1) * pow2 64 + (v a0 + v b0) / pow2 64 * pow2 64) % pow2 128 + ((v a0 + v b0) % pow2 64) % pow2 128;
  };
  assert (v r2 * pow2 64 + v r0 ==
    ((v a1 + v b1) * pow2 64 + (v a0 + v b0) / pow2 64 * pow2 64) % pow2 128 + ((v a0 + v b0) % pow2 64) % pow2 128);
  assert (v r2 * pow2 64 + v r0 < pow2 128);
  add_mod_small ((v a1 + v b1) * pow2 64 + (v a0 + v b0) / pow2 64 * pow2 64) ((v a0 + v b0) % pow2 64) (pow2 128);
  FStar.Math.Lemmas.euclidean_division_definition (v a0 + v b0) (pow2 64);
  assert (v r2 * pow2 64 + v r0 == ((v a1 + v b1) * pow2 64 + v a0 + v b0) % pow2 128)
