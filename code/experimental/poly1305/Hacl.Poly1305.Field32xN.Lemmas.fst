module Hacl.Poly1305.Field32xN.Lemmas

open Lib.IntTypes
open Lib.IntVector
open Lib.Sequence
open FStar.Mul

open Hacl.Spec.Poly1305.Vec
include Hacl.Spec.Poly1305.Field32xN

#reset-options "--z3rlimit 100 --using_facts_from '* -FStar.Seq'"

val lemma_prime: unit ->
  Lemma (pow2 130 % prime = 5)
let lemma_prime () =
  assert_norm (pow2 130 % prime = 5 % prime);
  assert_norm (5 < prime);
  FStar.Math.Lemmas.modulo_lemma 5 prime

val lemma_mult_le: a:nat -> b:nat -> c:nat -> d:nat
  -> Lemma
    (requires a <= b /\ c <= d)
    (ensures  a * c <= b * d)
let lemma_mult_le a b c d = ()

val lemma_mul_assos_3:
  a:nat -> b:nat -> c:nat ->
  Lemma (a * b * c == a * (b * c))
let lemma_mul_assos_3 a b c = ()

val lemma_mul_assos_4:
  a:nat -> b:nat -> c:nat -> d:nat ->
  Lemma (a * b * c * d == a * (b * c * d))
let lemma_mul_assos_4 a b c d = ()

val lemma_mul_assos_5:
  a:nat -> b:nat -> c:nat -> d:nat -> e:nat ->
  Lemma (a * b * c * d * e == a * (b * c * d * e))
let lemma_mul_assos_5 a b c d e = ()

val lemma_mul_assos_6:
  a:nat -> b:nat -> c:nat -> d:nat -> e:nat -> f:nat ->
  Lemma (a * b * c * d * e * f == a * (b * c * d * e * f))
let lemma_mul_assos_6 a b c d e f = ()

val lemma_mul5_distr_l:
  a:nat -> b:nat -> c:nat -> d:nat -> e:nat -> f:nat ->
  Lemma (a * (b + c + d + e + f) == a * b + a * c + a * d + a * e + a * f)
let lemma_mul5_distr_l a b c d e f = ()

val lemma_mul5_distr_r:
  a:nat -> b:nat -> c:nat -> d:nat -> e:nat -> f:nat ->
  Lemma ((a + b + c + d + e) * f == a * f + b * f + c * f + d * f + e * f)
let lemma_mul5_distr_r a b c d e f = ()

val fadd5_eval_lemma_i:
    #w:lanes
  -> f1:felem5 w
  -> f2:felem5 w
  -> i:nat{i < w}
  -> Lemma
    (requires felem_fits5 f1 (1,2,1,1,1) /\ felem_fits5 f2 (1,1,1,1,1))
    (ensures  (feval5 (fadd5 f1 f2)).[i] == pfadd (feval5 f1).[i] (feval5 f2).[i])
let fadd5_eval_lemma_i #w f1 f2 i =
  let (f10, f11, f12, f13, f14) = f1 in
  let (f20, f21, f22, f23, f24) = f2 in
  let o = fadd5 f1 f2 in
  let (o0, o1, o2, o3, o4) = o in

  FStar.Math.Lemmas.modulo_lemma (v ((vec_v f10).[i]) + v ((vec_v f20).[i])) (pow2 64);
  FStar.Math.Lemmas.modulo_lemma (v ((vec_v f11).[i]) + v ((vec_v f21).[i])) (pow2 64);
  FStar.Math.Lemmas.modulo_lemma (v ((vec_v f12).[i]) + v ((vec_v f22).[i])) (pow2 64);
  FStar.Math.Lemmas.modulo_lemma (v ((vec_v f13).[i]) + v ((vec_v f23).[i])) (pow2 64);
  FStar.Math.Lemmas.modulo_lemma (v ((vec_v f14).[i]) + v ((vec_v f24).[i])) (pow2 64);
  assert (
    as_nat5 ((vec_v o0).[i],(vec_v o1).[i],(vec_v o2).[i],(vec_v o3).[i],(vec_v o4).[i]) ==
    as_nat5 ((vec_v f10).[i],(vec_v f11).[i],(vec_v f12).[i],(vec_v f13).[i],(vec_v f14).[i]) +
    as_nat5 ((vec_v f20).[i],(vec_v f21).[i],(vec_v f22).[i],(vec_v f23).[i],(vec_v f24).[i]));
  FStar.Math.Lemmas.lemma_mod_plus_distr_l
    (as_nat5 ((vec_v f10).[i],(vec_v f11).[i],(vec_v f12).[i],(vec_v f13).[i],(vec_v f14).[i]))
    (as_nat5 ((vec_v f20).[i],(vec_v f21).[i],(vec_v f22).[i],(vec_v f23).[i],(vec_v f24).[i])) prime;
  FStar.Math.Lemmas.lemma_mod_plus_distr_r
    ((as_nat5 ((vec_v f10).[i],(vec_v f11).[i],(vec_v f12).[i],(vec_v f13).[i],(vec_v f14).[i])) % prime)
    (as_nat5 ((vec_v f20).[i],(vec_v f21).[i],(vec_v f22).[i],(vec_v f23).[i],(vec_v f24).[i])) prime;
  assert ((feval5 o).[i] == pfadd (feval5 f1).[i] (feval5 f2).[i])

val smul_felem5_fits_lemma_i:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32
  -> u1:uint64xN w
  -> f2:uint64xN w
  -> i:nat{i < w}
  -> Lemma
    (requires felem_fits1 u1 m1 /\ felem_fits1 f2 m2)
    (ensures  uint_v (vec_v (vec_mul_mod f2 u1)).[i] <= m1 * m2 * max26 * max26)
let smul_felem5_fits_lemma_i #w #m1 #m2 u1 f2 i =
  let o = vec_mul_mod f2 u1 in
  assert (uint_v (vec_v o).[i] == (uint_v (vec_v f2).[i] * uint_v (vec_v u1).[i]) % pow2 64);
  lemma_mult_le (uint_v (vec_v f2).[i]) (m2 * max26) (uint_v (vec_v u1).[i]) (m1 * max26);
  assert (uint_v (vec_v f2).[i] * uint_v (vec_v u1).[i] <= m1 * m2 * max26 * max26);
  FStar.Math.Lemmas.modulo_lemma (uint_v (vec_v f2).[i] * uint_v (vec_v u1).[i]) (pow2 64);
  assert (uint_v (vec_v o).[i] == uint_v (vec_v f2).[i] * uint_v (vec_v u1).[i])

val smul_mod_lemma:
    #m1:scale32
  -> #m2:scale32
  -> a:nat{a <= m1 * max26}
  -> b:nat{b <= m2 * max26}
  -> c:nat{c == a * b % pow2 64}
  -> Lemma (c == a * b)
let smul_mod_lemma #m1 #m2 a b c =
  lemma_mult_le a (m1 * max26) b (m2 * max26);
  assert (a * b <= m1 * m2 * max26 * max26);
  FStar.Math.Lemmas.modulo_lemma (a * b) (pow2 64)

val smul_lemma:
    vu1:nat -> f20:nat -> f21:nat -> f22:nat -> f23:nat -> f24:nat
  -> Lemma
     (vu1 * (f20 + f21 * pow26 + f22 * pow26 * pow26 +
      f23 * pow26 * pow26 * pow26 + f24 * pow26 * pow26 * pow26 * pow26) ==
      f20 * vu1 + f21 * vu1 * pow26 + f22 * vu1 * pow26 * pow26 +
      f23 * vu1 * pow26 * pow26 * pow26 + f24 * vu1 * pow26 * pow26 * pow26 * pow26)
let smul_lemma vu1 f20 f21 f22 f23 f24 = ()

val smul_felem5_eval_lemma_i:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32_5
  -> u1:uint64xN w
  -> f2:felem5 w
  -> i:nat{i < w}
  -> Lemma
    (requires felem_fits1 u1 m1 /\ felem_fits5 f2 m2)
    (ensures (fas_nat5 (smul_felem5 #w u1 f2)).[i] == (uint64xN_v u1).[i] * (fas_nat5 f2).[i])
let smul_felem5_eval_lemma_i #w #m1 #m2 u1 f2 i =
  let o = smul_felem5 #w u1 f2 in
  let (m20, m21, m22, m23, m24) = m2 in
  let vu1 = (uint64xN_v u1).[i] in
  let (tf20, tf21, tf22, tf23, tf24) = as_tup64_i f2 i in
  let (to0, to1, to2, to3, to4) = as_tup64_i o i in

  smul_mod_lemma #m1 #m20 vu1 (v tf20) (v to0);
  smul_mod_lemma #m1 #m21 vu1 (v tf21) (v to1);
  smul_mod_lemma #m1 #m22 vu1 (v tf22) (v to2);
  smul_mod_lemma #m1 #m23 vu1 (v tf23) (v to3);
  smul_mod_lemma #m1 #m24 vu1 (v tf24) (v to4);

  assert ((fas_nat5 o).[i] == v tf20 * vu1 + v tf21 * vu1 * pow26 + v tf22 * vu1 * pow26 * pow26 +
    v tf23 * vu1 * pow26 * pow26 * pow26 + v tf24 * vu1 * pow26 * pow26 * pow26 * pow26);

  assert (vu1 * (fas_nat5 f2).[i] == vu1 * (v tf20 + v tf21 * pow26 + v tf22 * pow26 * pow26 +
    v tf23 * pow26 * pow26 * pow26 + v tf24 * pow26 * pow26 * pow26 * pow26));

  smul_lemma vu1 (v tf20) (v tf21) (v tf22) (v tf23) (v tf24)

val smul_add_felem5_fits_lemma_i:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32
  -> #m3:scale64
  -> u1:uint64xN w
  -> f2:uint64xN w
  -> acc1:uint64xN w
  -> i:nat{i < w}
  -> Lemma
    (requires
      felem_fits1 u1 m1 /\ felem_fits1 f2 m2 /\
      felem_wide_fits1 acc1 m3 /\ m3 + m1 * m2 <= 4096)
    (ensures
      uint_v (vec_v (vec_add_mod acc1 (vec_mul_mod f2 u1))).[i] <= (m3 + m1 * m2) * max26 * max26)
let smul_add_felem5_fits_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 i =
  let o = vec_add_mod acc1 (vec_mul_mod f2 u1) in
  assert (v (vec_v o).[i] == (v (vec_v acc1).[i] + (v (vec_v f2).[i] * v (vec_v u1).[i]) % pow2 64) % pow2 64);
  lemma_mult_le (uint_v (vec_v f2).[i]) (m2 * max26) (uint_v (vec_v u1).[i]) (m1 * max26);
  assert (uint_v (vec_v f2).[i] * uint_v (vec_v u1).[i] <= m1 * m2 * max26 * max26);
  FStar.Math.Lemmas.modulo_lemma (uint_v (vec_v f2).[i] * uint_v (vec_v u1).[i]) (pow2 64);
  assert (v (vec_v o).[i] == (v (vec_v acc1).[i] + v (vec_v f2).[i] * v (vec_v u1).[i]) % pow2 64);
  assert (v (vec_v acc1).[i] + v (vec_v f2).[i] * v (vec_v u1).[i] <= m3 * max26 * max26 + m1 * m2 * max26 * max26);
  assert (v (vec_v acc1).[i] + v (vec_v f2).[i] * v (vec_v u1).[i] <= (m3 + m1 * m2) * max26 * max26)

val smul_add_mod_lemma:
    #m1:scale32
  -> #m2:scale32
  -> #m3:scale64
  -> a:nat{a <= m1 * max26}
  -> b:nat{b <= m2 * max26}
  -> c:nat{c <= m3 * max26 * max26 /\ m3 + m1 * m2 <= 4096}
  -> d:nat{d == (c + (a * b) % pow2 64) % pow2 64}
  -> Lemma (d == c + a * b)
let smul_add_mod_lemma #m1 #m2 #m3 a b c d =
  lemma_mult_le a (m1 * max26) b (m2 * max26);
  assert (a * b <= m1 * m2 * max26 * max26);
  FStar.Math.Lemmas.modulo_lemma (a * b) (pow2 64)

val smul_add_lemma:
  va0:nat -> va1:nat -> va2:nat -> va3:nat -> va4:nat -> vu1:nat ->
  vf20:nat -> vf21:nat -> vf22:nat -> vf23:nat -> vf24:nat ->
  Lemma (
    va0 + va1 * pow26 + va2 * pow26 * pow26 +
    va3 * pow26 * pow26 * pow26 + va4 * pow26 * pow26 * pow26 * pow26 +
    vu1 * vf20 + vu1 * vf21 * pow26 + vu1 * vf22 * pow26 * pow26 +
    vu1 * vf23 * pow26 * pow26 * pow26 + vu1 * vf24 * pow26 * pow26 * pow26 * pow26 ==
    va0 + va1 * pow26 + va2 * pow26 * pow26 +
    va3 * pow26 * pow26 * pow26 + va4 * pow26 * pow26 * pow26 * pow26 +
    vu1 * (vf20 + vf21 * pow26 + vf22 * pow26 * pow26 +
    vf23 * pow26 * pow26 * pow26 + vf24 * pow26 * pow26 * pow26 * pow26))
let smul_add_lemma va0 va1 va2 va3 va4 vu1 vf20 vf21 vf22 vf23 vf24 = ()

val smul_add_felem5_eval_lemma_i:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32_5
  -> #m3:scale64_5
  -> u1:uint64xN w
  -> f2:felem5 w
  -> acc1:felem_wide5 w
  -> i:nat{i < w}
  -> Lemma
    (requires
      felem_fits1 u1 m1 /\ felem_fits5 f2 m2 /\
      felem_wide_fits5 acc1 m3 /\ m3 +* m1 *^ m2 <=* s64x5 4096)
    (ensures
      (fas_nat5 (smul_add_felem5 #w u1 f2 acc1)).[i] ==
	(fas_nat5 acc1).[i] + (uint64xN_v u1).[i] * (fas_nat5 f2).[i])
let smul_add_felem5_eval_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 i =
  let o = smul_add_felem5 #w u1 f2 acc1 in
  let (m20, m21, m22, m23, m24) = m2 in
  let (m30, m31, m32, m33, m34) = m3 in
  let vu1 = (uint64xN_v u1).[i] in
  let (tf20, tf21, tf22, tf23, tf24) = as_tup64_i f2 i in
  let (ta0, ta1, ta2, ta3, ta4) = as_tup64_i acc1 i in
  let (to0, to1, to2, to3, to4) = as_tup64_i o i in

  smul_add_mod_lemma #m1 #m20 #m30 vu1 (v tf20) (v ta0) (v to0);
  smul_add_mod_lemma #m1 #m21 #m31 vu1 (v tf21) (v ta1) (v to1);
  smul_add_mod_lemma #m1 #m22 #m32 vu1 (v tf22) (v ta2) (v to2);
  smul_add_mod_lemma #m1 #m23 #m33 vu1 (v tf23) (v ta3) (v to3);
  smul_add_mod_lemma #m1 #m24 #m34 vu1 (v tf24) (v ta4) (v to4);

  assert ((fas_nat5 o).[i] ==
    v ta0 + vu1 * v tf20 + (v ta1 + vu1 * v tf21) * pow26 + (v ta2 + vu1 * v tf22) * pow26 * pow26 +
    (v ta3 + vu1 * v tf23) * pow26 * pow26 * pow26 + (v ta4 + vu1 * v tf24) * pow26 * pow26 * pow26 * pow26);

  assert ((fas_nat5 o).[i] ==
    v ta0 + v ta1 * pow26 + v ta2 * pow26 * pow26 +
    v ta3 * pow26 * pow26 * pow26 + v ta4 * pow26 * pow26 * pow26 * pow26 +
    vu1 * v tf20 + vu1 * v tf21 * pow26 + vu1 * v tf22 * pow26 * pow26 +
    vu1 * v tf23 * pow26 * pow26 * pow26 + vu1 * v tf24 * pow26 * pow26 * pow26 * pow26);

  assert ((fas_nat5 acc1).[i] + vu1 * (fas_nat5 f2).[i] ==
    v ta0 + v ta1 * pow26 + v ta2 * pow26 * pow26 +
    v ta3 * pow26 * pow26 * pow26 + v ta4 * pow26 * pow26 * pow26 * pow26 +
    vu1 * (v tf20 + v tf21 * pow26 + v tf22 * pow26 * pow26 +
    v tf23 * pow26 * pow26 * pow26 + v tf24 * pow26 * pow26 * pow26 * pow26));
  smul_add_lemma (v ta0) (v ta1) (v ta2) (v ta3) (v ta4) vu1 (v tf20) (v tf21) (v tf22) (v tf23) (v tf24)

val lemma_fmul5_pow26:
  r:tup64_5
  -> Lemma
    (requires
      (let (r0, r1, r2, r3, r4) = r in v r4 * 5 <= 10 * pow26))
    (ensures
      (let (r0, r1, r2, r3, r4) = r in
      (pow26 * as_nat5 r) % prime == as_nat5 (r4 *! u64 5, r0, r1, r2, r3) % prime))
let lemma_fmul5_pow26 r =
  let (r0, r1, r2, r3, r4) = r in
  assert (pow26 * as_nat5 r ==
    pow26 * (v r0 + v r1 * pow26 + v r2 * pow26 * pow26 +
    v r3 * pow26 * pow26 * pow26 + v r4 * pow26 * pow26 * pow26 * pow26));
  lemma_mul5_distr_l pow26 (v r0) (v r1 * pow26) (v r2 * pow26 * pow26)
    (v r3 * pow26 * pow26 * pow26) (v r4 * pow26 * pow26 * pow26 * pow26);

  let p26r0123 = pow26 * v r0 + pow26 * v r1 * pow26 +
    pow26 * v r2 * pow26 * pow26 + pow26 * v r3 * pow26 * pow26 * pow26 in
  let p26r4 = pow26 * v r4 * pow26 * pow26 * pow26 * pow26 in
  assert ((pow26 * as_nat5 r) % prime == (p26r0123 + p26r4) % prime);

  FStar.Math.Lemmas.lemma_mod_plus_distr_r p26r0123 p26r4 prime;
  assert_norm (p26r4 % prime == (v r4 * pow2 130) % prime);
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v r4) (pow2 130) prime;
  lemma_prime ();
  assert_norm ((v r4 * pow2 130) % prime == (v r4 * 5) % prime);
  FStar.Math.Lemmas.lemma_mod_plus_distr_r p26r0123 (v r4 * 5) prime

val lemma_fmul5_pow26_pow26:
    r:tup64_5
  -> Lemma
    (requires
     (let (r0, r1, r2, r3, r4) = r in
      v r4 * 5 <= 10 * pow26 /\ v r3 * 5 <= 10 * pow26))
    (ensures
      (let (r0, r1, r2, r3, r4) = r in
      (pow26 * pow26 * as_nat5 r) % prime ==
       as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2) % prime))
let lemma_fmul5_pow26_pow26 r =
  let (r0, r1, r2, r3, r4) = r in
  let p26r = pow26 * as_nat5 r in
  FStar.Math.Lemmas.lemma_mod_mul_distr_r pow26 p26r prime;
  assert ((pow26 * pow26 * as_nat5 r) % prime == (pow26 * (p26r % prime)) % prime);
  lemma_fmul5_pow26 r;
  assert ((pow26 * pow26 * as_nat5 r) % prime ==
    (pow26 * (as_nat5 (r4 *! u64 5, r0, r1, r2, r3) % prime)) % prime);
  FStar.Math.Lemmas.lemma_mod_mul_distr_r pow26 (as_nat5 (r4 *! u64 5, r0, r1, r2, r3)) prime;
  lemma_fmul5_pow26 (r4 *! u64 5, r0, r1, r2, r3);
  FStar.Math.Lemmas.lemma_mod_mul_distr_r pow26 (as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2)) prime

val lemma_fmul5_pow26_pow26_pow26:
  r:tup64_5
  -> Lemma
    (requires
     (let (r0, r1, r2, r3, r4) = r in
      v r4 * 5 <= 10 * pow26 /\ v r3 * 5 <= 10 * pow26 /\
      v r2 * 5 <= 10 * pow26))
    (ensures
      (let (r0, r1, r2, r3, r4) = r in
      (pow26 * pow26 * pow26 * as_nat5 r) % prime ==
       as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1) % prime))
let lemma_fmul5_pow26_pow26_pow26 r =
  let (r0, r1, r2, r3, r4) = r in
  let p26p26r = pow26 * pow26 * as_nat5 r in
  FStar.Math.Lemmas.lemma_mod_mul_distr_r pow26 p26p26r prime;
  assert ((pow26 * pow26 * pow26 * as_nat5 r) % prime == (pow26 * (p26p26r % prime)) % prime);
  lemma_fmul5_pow26_pow26 r;
  assert ((pow26 * pow26 * pow26 * as_nat5 r) % prime ==
    (pow26 * (as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2) % prime)) % prime);
  FStar.Math.Lemmas.lemma_mod_mul_distr_r pow26 (as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2)) prime;
  lemma_fmul5_pow26 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2);
  FStar.Math.Lemmas.lemma_mod_mul_distr_r pow26 (as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1)) prime

val lemma_fmul5_pow26_pow26_pow26_pow26:
    r:tup64_5
  -> Lemma
    (requires
      (let (r0, r1, r2, r3, r4) = r in
      v r4 * 5 <= 10 * pow26 /\ v r3 * 5 <= 10 * pow26 /\
      v r2 * 5 <= 10 * pow26 /\ v r1 * 5 <= 10 * pow26))
    (ensures
      (let (r0, r1, r2, r3, r4) = r in
      (pow26 * pow26 * pow26 * pow26 * as_nat5 r) % prime ==
       as_nat5 (r1 *! u64 5, r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0) % prime))
let lemma_fmul5_pow26_pow26_pow26_pow26 r =
  let (r0, r1, r2, r3, r4) = r in
  //lemma_mul_assos_5 pow26 pow26 pow26 pow26 (as_nat5 r);
  let p26p26p26r = pow26 * pow26 * pow26 * as_nat5 r in
  FStar.Math.Lemmas.lemma_mod_mul_distr_r pow26 p26p26p26r prime;
  assert ((pow26 * pow26 * pow26 * pow26 * as_nat5 r) % prime == (pow26 * (p26p26p26r % prime)) % prime);
  lemma_fmul5_pow26_pow26_pow26 r;
  assert ((pow26 * pow26 * pow26 * pow26 * as_nat5 r) % prime ==
    (pow26 * (as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1) % prime)) % prime);
  FStar.Math.Lemmas.lemma_mod_mul_distr_r pow26 (as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1)) prime;
  lemma_fmul5_pow26 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1);
  FStar.Math.Lemmas.lemma_mod_mul_distr_r pow26 (as_nat5 (r1 *! u64 5, r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0)) prime

val lemma_fmul5_1:
    f1:tup64_5{tup64_fits5 f1 (2, 3, 2, 2, 2)}
  -> r:tup64_5{tup64_fits5 r (1, 2, 1, 1, 1)}
  -> Lemma
    (requires
     (let (f10, f11, f12, f13, f14) = f1 in
      let (r0, r1, r2, r3, r4) = r in
     (as_nat5 f1 * as_nat5 r) % prime ==
     (v f10 * as_nat5 r +
      v f11 * pow26 * as_nat5 r +
      v f12 * pow26 * pow26 * as_nat5 r +
      v f13 * pow26 * pow26 * pow26 * as_nat5 r +
      v f14 * pow26 * pow26 * pow26 * pow26 * as_nat5 r) % prime))
   (ensures
    (let (f10, f11, f12, f13, f14) = f1 in
     let (r0, r1, r2, r3, r4) = r in
    (as_nat5 f1 * as_nat5 r) % prime ==
    (v f10 * as_nat5 r +
     v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3) +
     v f12 * pow26 * pow26 * as_nat5 r +
     v f13 * pow26 * pow26 * pow26 * as_nat5 r +
     v f14 * pow26 * pow26 * pow26 * pow26 * as_nat5 r) % prime))
let lemma_fmul5_1 f1 r =
  let (f10, f11, f12, f13, f14) = f1 in
  let (r0, r1, r2, r3, r4) = r in
  assert ((as_nat5 f1 * as_nat5 r) % prime ==
    (v f10 * as_nat5 r +
     v f11 * pow26 * as_nat5 r +
     v f12 * pow26 * pow26 * as_nat5 r +
     v f13 * pow26 * pow26 * pow26 * as_nat5 r +
     v f14 * pow26 * pow26 * pow26 * pow26 * as_nat5 r) % prime);
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (v f11 * pow26 * as_nat5 r)
    (v f10 * as_nat5 r +
     v f12 * pow26 * pow26 * as_nat5 r +
     v f13 * pow26 * pow26 * pow26 * as_nat5 r +
     v f14 * pow26 * pow26 * pow26 * pow26 * as_nat5 r) prime;
  lemma_mul_assos_3 (v f11) pow26 (as_nat5 r);
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v f11) (pow26 * as_nat5 r) prime;
  lemma_fmul5_pow26 (r0, r1, r2, r3, r4);
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v f11) (as_nat5 (r4 *! u64 5, r0, r1, r2, r3)) prime;
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3))
    (v f10 * as_nat5 r +
     v f12 * pow26 * pow26 * as_nat5 r +
     v f13 * pow26 * pow26 * pow26 * as_nat5 r +
     v f14 * pow26 * pow26 * pow26 * pow26 * as_nat5 r) prime

val lemma_fmul5_2:
    f1:tup64_5{tup64_fits5 f1 (2, 3, 2, 2, 2)}
  -> r:tup64_5{tup64_fits5 r (1, 2, 1, 1, 1)}
  -> Lemma
    (requires
     (let (f10, f11, f12, f13, f14) = f1 in
      let (r0, r1, r2, r3, r4) = r in
     (as_nat5 f1 * as_nat5 r) % prime ==
     (v f10 * as_nat5 r +
      v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3) +
      v f12 * pow26 * pow26 * as_nat5 r +
      v f13 * pow26 * pow26 * pow26 * as_nat5 r +
      v f14 * pow26 * pow26 * pow26 * pow26 * as_nat5 r) % prime))
   (ensures (let (f10, f11, f12, f13, f14) = f1 in
     let (r0, r1, r2, r3, r4) = r in
    (as_nat5 f1 * as_nat5 r) % prime ==
    (v f10 * as_nat5 r +
     v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3) +
     v f12 * as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2) +
     v f13 * pow26 * pow26 * pow26 * as_nat5 r +
     v f14 * pow26 * pow26 * pow26 * pow26 * as_nat5 r) % prime))
let lemma_fmul5_2 f1 r =
  let (f10, f11, f12, f13, f14) = f1 in
  let (r0, r1, r2, r3, r4) = r in
  lemma_mul_assos_4 (v f12) pow26 pow26 (as_nat5 r);
  let p26p26r = pow26 * pow26 * as_nat5 r in
  assert ((as_nat5 f1 * as_nat5 r) % prime ==
    (v f10 * as_nat5 r +
     v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3) +
     v f12 * p26p26r +
     v f13 * pow26 * pow26 * pow26 * as_nat5 r +
     v f14 * pow26 * pow26 * pow26 * pow26 * as_nat5 r) % prime);

  FStar.Math.Lemmas.lemma_mod_plus_distr_l (v f12 * p26p26r)
    (v f10 * as_nat5 r +
     v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3) +
     v f13 * pow26 * pow26 * pow26 * as_nat5 r +
     v f14 * pow26 * pow26 * pow26 * pow26 * as_nat5 r) prime;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v f12) p26p26r prime;
  lemma_fmul5_pow26_pow26 r;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v f12) (as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2)) prime;
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (v f12 * as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2))
    (v f10 * as_nat5 r +
     v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3) +
     v f13 * pow26 * pow26 * pow26 * as_nat5 r +
     v f14 * pow26 * pow26 * pow26 * pow26 * as_nat5 r) prime

val lemma_fmul5_3:
    f1:tup64_5{tup64_fits5 f1 (2, 3, 2, 2, 2)}
  -> r:tup64_5{tup64_fits5 r (1, 2, 1, 1, 1)}
  -> Lemma
    (requires
     (let (f10, f11, f12, f13, f14) = f1 in
      let (r0, r1, r2, r3, r4) = r in
     (as_nat5 f1 * as_nat5 r) % prime ==
     (v f10 * as_nat5 r +
      v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3) +
      v f12 * as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2) +
      v f13 * pow26 * pow26 * pow26 * as_nat5 r +
      v f14 * pow26 * pow26 * pow26 * pow26 * as_nat5 r) % prime))
   (ensures (let (f10, f11, f12, f13, f14) = f1 in
     let (r0, r1, r2, r3, r4) = r in
    (as_nat5 f1 * as_nat5 r) % prime ==
    (v f10 * as_nat5 r +
     v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3) +
     v f12 * as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2) +
     v f13 * as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1) +
     v f14 * pow26 * pow26 * pow26 * pow26 * as_nat5 r) % prime))
let lemma_fmul5_3 f1 r =
  let (f10, f11, f12, f13, f14) = f1 in
  let (r0, r1, r2, r3, r4) = r in
  lemma_mul_assos_5 (v f13) pow26 pow26 pow26 (as_nat5 r);
  let p26p26p26r = pow26 * pow26 * pow26 * as_nat5 r in
  assert ((as_nat5 f1 * as_nat5 r) % prime ==
    (v f10 * as_nat5 r +
     v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3) +
     v f12 * as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2) +
     v f13 * p26p26p26r +
     v f14 * pow26 * pow26 * pow26 * pow26 * as_nat5 r) % prime);

  FStar.Math.Lemmas.lemma_mod_plus_distr_l (v f13 * p26p26p26r)
    (v f10 * as_nat5 r +
     v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3) +
     v f12 * as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2) +
     v f14 * pow26 * pow26 * pow26 * pow26 * as_nat5 r) prime;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v f13) p26p26p26r prime;
  lemma_fmul5_pow26_pow26_pow26 r;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v f13) (as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1)) prime;
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (v f13 * as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1))
    (v f10 * as_nat5 r +
     v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3) +
     v f12 * as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2) +
     v f14 * pow26 * pow26 * pow26 * pow26 * as_nat5 r) prime

val lemma_fmul5_4:
    f1:tup64_5{tup64_fits5 f1 (2, 3, 2, 2, 2)}
  -> r:tup64_5{tup64_fits5 r (1, 2, 1, 1, 1)}
  -> Lemma
    (requires
     (let (f10, f11, f12, f13, f14) = f1 in
      let (r0, r1, r2, r3, r4) = r in
     (as_nat5 f1 * as_nat5 r) % prime ==
     (v f10 * as_nat5 r +
      v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3) +
      v f12 * as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2) +
      v f13 * as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1) +
      v f14 * pow26 * pow26 * pow26 * pow26 * as_nat5 r) % prime))
   (ensures (let (f10, f11, f12, f13, f14) = f1 in
     let (r0, r1, r2, r3, r4) = r in
    (as_nat5 f1 * as_nat5 r) % prime ==
    (v f10 * as_nat5 r +
     v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3) +
     v f12 * as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2) +
     v f13 * as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1) +
     v f14 * as_nat5 (r1 *! u64 5, r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0)) % prime))
let lemma_fmul5_4 f1 r =
  let (f10, f11, f12, f13, f14) = f1 in
  let (r0, r1, r2, r3, r4) = r in
  lemma_mul_assos_6 (v f14) pow26 pow26 pow26 pow26 (as_nat5 r);
  let p26p26p26p26r = pow26 * pow26 * pow26 * pow26 * as_nat5 r in
  assert ((as_nat5 f1 * as_nat5 r) % prime ==
    (v f10 * as_nat5 r +
     v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3) +
     v f12 * as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2) +
     v f13 * as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1) +
     v f14 * p26p26p26p26r) % prime);

  FStar.Math.Lemmas.lemma_mod_plus_distr_l (v f14 * p26p26p26p26r)
    (v f10 * as_nat5 r +
     v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3) +
     v f12 * as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2) +
     v f13 * as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1)) prime;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v f14) p26p26p26p26r prime;
  lemma_fmul5_pow26_pow26_pow26_pow26 r;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v f14) (as_nat5 (r1 *! u64 5, r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0)) prime;
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (v f14 * as_nat5 (r1 *! u64 5, r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0))
    (v f10 * as_nat5 r +
     v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3) +
     v f12 * as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2) +
     v f13 * as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1)) prime

val mul_felem5_lemma:
    f1:tup64_5{tup64_fits5 f1 (2, 3, 2, 2, 2)}
  -> r:tup64_5{tup64_fits5 r (1, 2, 1, 1, 1)}
  -> Lemma
    (let (f10, f11, f12, f13, f14) = f1 in
     let (r0, r1, r2, r3, r4) = r in
     (as_pfelem5 f1) `pfmul` (as_pfelem5 r) ==
     (v f10 * as_nat5 (r0, r1, r2, r3, r4) +
      v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3) +
      v f12 * as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2) +
      v f13 * as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1) +
      v f14 * as_nat5 (r1 *! u64 5, r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0)) % prime)
let mul_felem5_lemma f1 r =
  let (f10, f11, f12, f13, f14) = f1 in
  let (r0, r1, r2, r3, r4) = r in
  assert ((as_nat5 f1 * as_nat5 r) % prime ==
    (v f10 + v f11 * pow26 + v f12 * pow26 * pow26 + v f13 * pow26 * pow26 * pow26 +
    v f14 * pow26 * pow26 * pow26 * pow26) * as_nat5 r % prime);
  lemma_mul5_distr_r (v f10) (v f11 * pow26) (v f12 * pow26 * pow26)
    (v f13 * pow26 * pow26 * pow26) (v f14 * pow26 * pow26 * pow26 * pow26) (as_nat5 r);
  lemma_fmul5_1 f1 r;
  lemma_fmul5_2 f1 r;
  lemma_fmul5_3 f1 r;
  lemma_fmul5_4 f1 r;
  FStar.Math.Lemmas.lemma_mod_mul_distr_l (as_nat5 f1) (as_nat5 r) prime;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (as_nat5 f1 % prime) (as_nat5 r) prime

val precomp_r5_as_tup64:
    #w:lanes
  -> r:felem5 w
  -> i:nat{i < w}
  -> Lemma
    (requires felem_fits5 r (1, 2, 1, 1, 1))
    (ensures
     (let r5 = precomp_r5 r in
      let (tr50, tr51, tr52, tr53, tr54) = as_tup64_i r5 i in
      let (tr0, tr1, tr2, tr3, tr4) = as_tup64_i r i in
      tr50 == tr0 *! u64 5 /\
      tr51 == tr1 *! u64 5 /\
      tr52 == tr2 *! u64 5 /\
      tr53 == tr3 *! u64 5 /\
      tr54 == tr4 *! u64 5))
let precomp_r5_as_tup64 #w r i =
  let r5 = precomp_r5 r in
  let (r50, r51, r52, r53, r54) = r5 in
  let (r0, r1, r2, r3, r4) = r in
  let (tr50, tr51, tr52, tr53, tr54) = as_tup64_i r5 i in
  let (tr0, tr1, tr2, tr3, tr4) = as_tup64_i r i in
  assert_norm (max26 = pow2 26 - 1);
  FStar.Math.Lemmas.modulo_lemma (5 * v tr0) (pow2 64);
  FStar.Math.Lemmas.modulo_lemma (5 * v tr1) (pow2 64);
  FStar.Math.Lemmas.modulo_lemma (5 * v tr2) (pow2 64);
  FStar.Math.Lemmas.modulo_lemma (5 * v tr3) (pow2 64);
  FStar.Math.Lemmas.modulo_lemma (5 * v tr4) (pow2 64);
  uintv_extensionality tr50 (tr0 *! u64 5);
  uintv_extensionality tr51 (tr1 *! u64 5);
  uintv_extensionality tr52 (tr2 *! u64 5);
  uintv_extensionality tr53 (tr3 *! u64 5);
  uintv_extensionality tr54 (tr4 *! u64 5)

val mul_felem5_eval_as_tup64:
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
     (let (r0, r1, r2, r3, r4) = r in
      let (f10, f11, f12, f13, f14) = f1 in
      let (r50, r51, r52, r53, r54) = r5 in
      let (tr0, tr1, tr2, tr3, tr4) = as_tup64_i r i in
      let (tf10, tf11, tf12, tf13, tf14) = as_tup64_i f1 i in
      (uint64xN_v f10).[i] * (fas_nat5 (r0,r1,r2,r3,r4)).[i] +
      (uint64xN_v f11).[i] * (fas_nat5 (r54,r0,r1,r2,r3)).[i] +
      (uint64xN_v f12).[i] * (fas_nat5 (r53,r54,r0,r1,r2)).[i] +
      (uint64xN_v f13).[i] * (fas_nat5 (r52,r53,r54,r0,r1)).[i] +
      (uint64xN_v f14).[i] * (fas_nat5 (r51,r52,r53,r54,r0)).[i] ==
     (v tf10 * as_nat5 (tr0, tr1, tr2, tr3, tr4) +
      v tf11 * as_nat5 (tr4 *! u64 5, tr0, tr1, tr2, tr3) +
      v tf12 * as_nat5 (tr3 *! u64 5, tr4 *! u64 5, tr0, tr1, tr2) +
      v tf13 * as_nat5 (tr2 *! u64 5, tr3 *! u64 5, tr4 *! u64 5, tr0, tr1) +
      v tf14 * as_nat5 (tr1 *! u64 5, tr2 *! u64 5, tr3 *! u64 5, tr4 *! u64 5, tr0))))
let mul_felem5_eval_as_tup64 #w f1 r r5 i =
  let (r0, r1, r2, r3, r4) = r in
  let (f10, f11, f12, f13, f14) = f1 in
  let (r50, r51, r52, r53, r54) = r5 in
  let (tr0, tr1, tr2, tr3, tr4) = as_tup64_i r i in
  let (tf10, tf11, tf12, tf13, tf14) = as_tup64_i f1 i in
  let (tr50, tr51, tr52, tr53, tr54) = as_tup64_i r5 i in
  assert (
    (uint64xN_v f10).[i] * (fas_nat5 (r0,r1,r2,r3,r4)).[i] +
    (uint64xN_v f11).[i] * (fas_nat5 (r54,r0,r1,r2,r3)).[i] +
    (uint64xN_v f12).[i] * (fas_nat5 (r53,r54,r0,r1,r2)).[i] +
    (uint64xN_v f13).[i] * (fas_nat5 (r52,r53,r54,r0,r1)).[i] +
    (uint64xN_v f14).[i] * (fas_nat5 (r51,r52,r53,r54,r0)).[i] ==
    v tf10 * as_nat5 (tr0,tr1,tr2,tr3,tr4) +
    v tf11 * as_nat5 (tr54,tr0,tr1,tr2,tr3) +
    v tf12 * as_nat5 (tr53,tr54,tr0,tr1,tr2) +
    v tf13 * as_nat5 (tr52,tr53,tr54,tr0,tr1) +
    v tf14 * as_nat5 (tr51,tr52,tr53,tr54,tr0));
  precomp_r5_as_tup64 #w r i

val carry26_lemma_i:
    #w:lanes
  -> l:uint64xN w
  -> cin:uint64xN w
  -> i:nat{i < w}
  -> Lemma
    (requires felem_fits1 l 2 /\ felem_fits1 cin 62)
    (ensures
     (let (l0, l1) = carry26 #w l cin in
      (uint64xN_v l0).[i] <= max26 /\ (uint64xN_v l1).[i] < 64 /\
      (uint64xN_v l).[i] + (uint64xN_v cin).[i] ==
	(uint64xN_v l1).[i] * pow2 26 + (uint64xN_v l0).[i]))
let carry26_lemma_i #w l cin i =
  let l = (vec_v l).[i] in
  let cin = (vec_v cin).[i] in
  let mask26 = u64 0x3ffffff in
  assert_norm (0x3ffffff = pow2 26 - 1);
  FStar.Math.Lemmas.modulo_lemma (v l + v cin) (pow2 64);
  let l' = l +! cin in
  let l0 = l' &. mask26 in
  let l1 = l' >>. 26ul in
  mod_mask_lemma l' 26ul;
  uintv_extensionality (mod_mask #U64 26ul) mask26;
  FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 (v l') 26 32;
  FStar.Math.Lemmas.pow2_minus 32 26

val carry26_wide_lemma_i:
    #w:lanes
  -> #m:scale64{m < 64}
  -> l:uint64xN w
  -> cin:uint64xN w
  -> i:nat{i < w}
  -> Lemma
    (requires felem_wide_fits1 l m /\ felem_fits1 cin 64)
    (ensures
     (let (l0, l1) = carry26 #w l cin in
      (uint64xN_v l0).[i] <= max26 /\ (uint64xN_v l1).[i] <= (m + 1) * max26 /\
      (uint64xN_v l).[i] + (uint64xN_v cin).[i] ==
	(uint64xN_v l1).[i] * pow2 26 + (uint64xN_v l0).[i]))
let carry26_wide_lemma_i #w #m l cin i =
  let l = (vec_v l).[i] in
  let cin = (vec_v cin).[i] in
  let mask26 = u64 0x3ffffff in
  assert_norm (0x3ffffff = pow2 26 - 1);
  FStar.Math.Lemmas.modulo_lemma (v l + v cin) (pow2 64);
  let l' = l +! cin in
  let l0 = l' &. mask26 in
  let l1 = l' >>. 26ul in
  mod_mask_lemma l' 26ul;
  uintv_extensionality (mod_mask #U64 26ul) mask26;
  FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 (v l') 26 32;
  FStar.Math.Lemmas.euclidean_division_definition (v l') (pow2 26)

val acc_inv_lemma_i:
    #w:lanes
  -> acc:felem5 w
  -> cin:uint64xN w
  -> i:nat{i < w}
  -> Lemma
    (requires
      felem_fits5 acc (1, 1, 1, 1, 1) /\
      uint64xN_fits cin 64)
    (ensures
      (let (i0, i1, i2, i3, i4) = acc in
       let i1' = vec_add_mod i1 cin in
       let acc1 = (i0, i1', i2, i3, i4) in
      (if uint_v (vec_v i1').[i] >= pow2 26 then
	 tup64_fits5 (as_tup64_i acc1 i) (1, 2, 1, 1, 1) /\
	 uint_v (vec_v i1').[i] % pow2 26 < 64
       else tup64_fits5 (as_tup64_i acc1 i) (1, 1, 1, 1, 1))))
let acc_inv_lemma_i #w acc cin i =
  let (i0, i1, i2, i3, i4) = acc in
  let i1' = vec_add_mod i1 cin in
  assert ((vec_v i1').[i] == (vec_v i1).[i] +. (vec_v cin).[i]);
  assert (v (vec_v i1).[i] + v (vec_v cin).[i] <= max26 + 63);
  assert_norm (max26 = pow2 26 - 1);
  FStar.Math.Lemmas.euclidean_division_definition (v (vec_v i1).[i] + v (vec_v cin).[i]) (pow2 26)

val acc_inv_lemma:
    #w:lanes
  -> acc:felem5 w
  -> cin:uint64xN w
  -> Lemma
    (requires
      felem_fits5 acc (1, 1, 1, 1, 1) /\
      uint64xN_fits cin 64)
    (ensures
      (let (i0, i1, i2, i3, i4) = acc in
       let i1' = vec_add_mod i1 cin in
       acc_inv_t (i0, i1', i2, i3, i4)))
let acc_inv_lemma #w acc cin =
  match w with
  | 1 ->
    acc_inv_lemma_i #w acc cin 0
  | 2 ->
    acc_inv_lemma_i #w acc cin 0;
    acc_inv_lemma_i #w acc cin 1
  | 4 ->
    acc_inv_lemma_i #w acc cin 0;
    acc_inv_lemma_i #w acc cin 1;
    acc_inv_lemma_i #w acc cin 2;
    acc_inv_lemma_i #w acc cin 3

val vec_smul_mod_fits_lemma:
    #w:lanes
  -> c4:uint64xN w
  -> Lemma
    (requires felem_fits1 c4 12)
    (ensures  felem_fits1 (vec_smul_mod c4 (u64 5)) 62)
let vec_smul_mod_fits_lemma #w c4 = ()

val carry_wide_felem5_lemma:
  vc0:nat -> vc1:nat -> vc2:nat -> vc3:nat -> vc4:nat ->
  vt0:nat -> vt1:nat -> vt2:nat -> vt3:nat -> vt4:nat ->
  Lemma (
    (vc0 * pow2 26 + vt0 + (vc1 * pow2 26 + vt1 - vc0) * pow26 +
    (vc2 * pow2 26 + vt2 - vc1) * pow26 * pow26 +
    (vc3 * pow2 26 + vt3 - vc2) * pow26 * pow26 * pow26 +
    (vc4 * pow2 26 + vt4 - vc3) * pow26 * pow26 * pow26 * pow26) % prime ==
    (vt0 + vc4 * 5 + vt1 * pow26 + vt2 * pow26 * pow26 +
     vt3 * pow26 * pow26 * pow26 + vt4 * pow26 * pow26 * pow26 * pow26) % prime)
let carry_wide_felem5_lemma vc0 vc1 vc2 vc3 vc4 vt0 vt1 vt2 vt3 vt4 =
  assert_norm (pow26 = pow2 26);
  assert (
    vc0 * pow2 26 + vt0 + (vc1 * pow2 26 + vt1 - vc0) * pow26 +
    (vc2 * pow2 26 + vt2 - vc1) * pow26 * pow26 +
    (vc3 * pow2 26 + vt3 - vc2) * pow26 * pow26 * pow26 +
    (vc4 * pow2 26 + vt4 - vc3) * pow26 * pow26 * pow26 * pow26 ==
    vt0 + vc4 * pow26 * pow26 * pow26 * pow26 * pow26 + vt1 * pow26 + vt2 * pow26 * pow26 +
    vt3 * pow26 * pow26 * pow26 + vt4 * pow26 * pow26 * pow26 * pow26);
  FStar.Math.Lemmas.lemma_mod_plus_distr_r
   (vt0 + vt1 * pow26 + vt2 * pow26 * pow26 + vt3 * pow26 * pow26 * pow26 +
    vt4 * pow26 * pow26 * pow26 * pow26) (vc4 * pow26 * pow26 * pow26 * pow26 * pow26) prime;
  assert_norm (pow26 * pow26 * pow26 * pow26 * pow26 = pow2 130);
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (vc4) (pow2 130) prime;
  lemma_prime ();
  assert ((vc4 * pow26 * pow26 * pow26 * pow26 * pow26) % prime == (vc4 * 5) % prime);
  FStar.Math.Lemmas.lemma_mod_plus_distr_r
   (vt0 + vt1 * pow26 + vt2 * pow26 * pow26 + vt3 * pow26 * pow26 * pow26 +
    vt4 * pow26 * pow26 * pow26 * pow26) (vc4 * 5) prime
