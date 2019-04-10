module Hacl.Poly1305.Field32xN.Lemmas

open Lib.IntTypes
open Lib.IntVector
open Lib.Sequence
open FStar.Mul

open Hacl.Spec.Poly1305.Vec
include Hacl.Spec.Poly1305.Field32xN

#reset-options "--z3rlimit 20 --using_facts_from '* -FStar.Seq' --max_fuel 0 --max_ifuel 0"

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
let lemma_mul_assos_6 a b c d e f =
  let open FStar.Calc in
  calc (==) {
      a * b * c * d * e * f;
    == { lemma_mul_assos_5 a b c d e }
      (a * (b * c * d * e)) * f;
    == { FStar.Math.Lemmas.paren_mul_right a (b * c * d * e) f }
      a * (b * c * d * e * f);
  }

val lemma_mul5_distr_l:
  a:nat -> b:nat -> c:nat -> d:nat -> e:nat -> f:nat ->
  Lemma (a * (b + c + d + e + f) == a * b + a * c + a * d + a * e + a * f)
let lemma_mul5_distr_l a b c d e f = ()

val lemma_mul5_distr_r:
  a:nat -> b:nat -> c:nat -> d:nat -> e:nat -> f:nat ->
  Lemma ((a + b + c + d + e) * f == a * f + b * f + c * f + d * f + e * f)
let lemma_mul5_distr_r a b c d e f = ()

#push-options "--max_ifuel 1"
val fadd5_eval_lemma_i:
    #w:lanes
  -> f1:felem5 w
  -> f2:felem5 w
  -> i:nat{i < w}
  -> Lemma
    (requires felem_fits5 f1 (1,2,1,1,1) /\ felem_fits5 f2 (1,1,1,1,1))
    (ensures  (feval5 (fadd5 f1 f2)).[i] == pfadd (feval5 f1).[i] (feval5 f2).[i])
let fadd5_eval_lemma_i #w f1 f2 i =
  let o = fadd5 f1 f2 in
  let (f10, f11, f12, f13, f14) = as_tup64_i f1 i in
  let (f20, f21, f22, f23, f24) = as_tup64_i f2 i in
  let (o0, o1, o2, o3, o4) = as_tup64_i o i in

  FStar.Math.Lemmas.modulo_lemma (v f10 + v f20) (pow2 64);
  FStar.Math.Lemmas.modulo_lemma (v f11 + v f21) (pow2 64);
  FStar.Math.Lemmas.modulo_lemma (v f12 + v f20) (pow2 64);
  FStar.Math.Lemmas.modulo_lemma (v f13 + v f23) (pow2 64);
  FStar.Math.Lemmas.modulo_lemma (v f14 + v f24) (pow2 64);
  assert (as_nat5 (o0, o1, o2, o3, o4) ==
    as_nat5 (f10, f11, f12, f13, f14) + as_nat5 (f20, f21, f22, f23, f24));
  FStar.Math.Lemmas.lemma_mod_plus_distr_l
    (as_nat5 (f10, f11, f12, f13, f14)) (as_nat5 (f20, f21, f22, f23, f24)) prime;
  FStar.Math.Lemmas.lemma_mod_plus_distr_r
    (as_nat5 (f10, f11, f12, f13, f14) % prime) (as_nat5 (f20, f21, f22, f23, f24)) prime
#pop-options

#set-options "--z3rlimit 100"

val smul_felem5_fits_lemma_i:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32
  -> u1:uint64xN w
  -> f2:uint64xN w
  -> i:nat{i < w}
  -> Lemma
    (requires felem_fits1 u1 m1 /\ felem_fits1 f2 m2)
    (ensures  (uint64xN_v (vec_mul_mod f2 u1)).[i] <= m1 * m2 * max26 * max26)
let smul_felem5_fits_lemma_i #w #m1 #m2 u1 f2 i =
  let o = vec_mul_mod f2 u1 in
  assert ((uint64xN_v o).[i] == ((uint64xN_v f2).[i] * (uint64xN_v u1).[i]) % pow2 64);
  lemma_mult_le (uint64xN_v f2).[i] (m2 * max26) (uint64xN_v u1).[i] (m1 * max26);
  assert ((uint64xN_v f2).[i] * (uint64xN_v u1).[i] <= m1 * m2 * max26 * max26);
  FStar.Math.Lemmas.modulo_lemma ((uint64xN_v f2).[i] * (uint64xN_v u1).[i]) (pow2 64);
  assert ((uint64xN_v o).[i] == (uint64xN_v f2).[i] * (uint64xN_v u1).[i])

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

#push-options "--max_ifuel 1"
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
#pop-options

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
      (uint64xN_v (vec_add_mod acc1 (vec_mul_mod f2 u1))).[i] <= (m3 + m1 * m2) * max26 * max26)
let smul_add_felem5_fits_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 i =
  assert_norm (max26 = pow2 26 - 1);
  let o = vec_add_mod acc1 (vec_mul_mod f2 u1) in
  assert ((uint64xN_v o).[i] == ((uint64xN_v acc1).[i] + ((uint64xN_v f2).[i] * (uint64xN_v u1).[i]) % pow2 64) % pow2 64);
  lemma_mult_le (uint64xN_v f2).[i] (m2 * max26) (uint64xN_v u1).[i] (m1 * max26);
  assert ((uint64xN_v f2).[i] * (uint64xN_v u1).[i] <= m1 * m2 * max26 * max26);
  FStar.Math.Lemmas.modulo_lemma ((uint64xN_v f2).[i] * (uint64xN_v u1).[i]) (pow2 64);
  assert ((uint64xN_v o).[i] == ((uint64xN_v acc1).[i] + (uint64xN_v f2).[i] * (uint64xN_v u1).[i]) % pow2 64);
  assert ((uint64xN_v acc1).[i] + (uint64xN_v f2).[i] * (uint64xN_v u1).[i] <= m3 * max26 * max26 + m1 * m2 * max26 * max26);
  assert ((uint64xN_v acc1).[i] + (uint64xN_v f2).[i] * (uint64xN_v u1).[i] <= (m3 + m1 * m2) * max26 * max26)

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

#push-options "--max_ifuel 1"
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
#pop-options

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

val carry26_lemma_i:
    #w:lanes
  -> l:uint64xN w
  -> cin:uint64xN w
  -> i:nat{i < w}
  -> Lemma
    (requires felem_fits1 l 2 /\ uint64xN_fits cin (71 * max26))
    (ensures
     (let (l0, l1) = carry26 #w l cin in
      (uint64xN_v l0).[i] <= max26 /\ (uint64xN_v l1).[i] < 73 /\
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

val carry26_fits_lemma:
    #w:lanes
  -> l:uint64xN w
  -> cin:uint64xN w
  -> Lemma
    (requires
      felem_fits1 l 2 /\ uint64xN_fits cin (71 * max26))
    (ensures
     (let (l0, l1) = carry26 #w l cin in
      felem_fits1 l0 1 /\ uint64xN_fits l1 73))
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
    (requires felem_fits1 l 2 /\ uint64xN_fits cin (71 * max26))
    (ensures
     (let (l0, l1) = carry26 #w l cin in
      felem_fits1 l0 1 /\ uint64xN_fits l1 73 /\
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

val acc_inv_lemma_i:
    #w:lanes
  -> acc:felem5 w
  -> cin:uint64xN w
  -> i:nat{i < w}
  -> Lemma
    (requires
      felem_fits5 acc (1, 1, 1, 1, 1) /\
      uint64xN_fits cin 73)
    (ensures
      (let (i0, i1, i2, i3, i4) = acc in
       let i1' = vec_add_mod i1 cin in
       let acc1 = (i0, i1', i2, i3, i4) in
      (if (uint64xN_v i1').[i] >= pow2 26 then
	 tup64_fits5 (as_tup64_i acc1 i) (1, 2, 1, 1, 1) /\
	 (uint64xN_v i1').[i] % pow2 26 < 73
       else tup64_fits5 (as_tup64_i acc1 i) (1, 1, 1, 1, 1))))
let acc_inv_lemma_i #w acc cin i =
  let (i0, i1, i2, i3, i4) = acc in
  let i1' = vec_add_mod i1 cin in
  assert ((vec_v i1').[i] == (vec_v i1).[i] +. (vec_v cin).[i]);
  assert ((uint64xN_v i1).[i] + (uint64xN_v cin).[i] <= max26 + 72);
  assert_norm (max26 = pow2 26 - 1);
  FStar.Math.Lemmas.euclidean_division_definition ((uint64xN_v i1).[i] + (uint64xN_v cin).[i]) (pow2 26)

val acc_inv_lemma:
    #w:lanes
  -> acc:felem5 w
  -> cin:uint64xN w
  -> Lemma
    (requires
      felem_fits5 acc (1, 1, 1, 1, 1) /\
      uint64xN_fits cin 73)
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
    (requires felem_fits1 c4 14)
    (ensures  uint64xN_fits (vec_smul_mod c4 (u64 5)) (71 * max26))
let vec_smul_mod_fits_lemma #w c4 = ()

val carry_wide_felem5_fits_lemma:
    #w:lanes
  -> inp:felem_wide5 w
  -> Lemma
    (requires felem_wide_fits5 inp (57, 37, 30, 21, 13))
    (ensures acc_inv_t (carry_wide_felem5 #w inp))
let carry_wide_felem5_fits_lemma #w inp =
  let (i0, i1, i2, i3, i4) = inp in
  let tmp0,c0 = carry26_wide i0 (zero w) in
  carry26_wide_fits_lemma #w #57 i0 (zero w);
  let tmp1,c1 = carry26_wide i1 c0 in
  carry26_wide_fits_lemma #w #37 i1 c0;
  let tmp2,c2 = carry26_wide i2 c1 in
  carry26_wide_fits_lemma #w #30 i2 c1;
  let tmp3,c3 = carry26_wide i3 c2 in
  carry26_wide_fits_lemma #w #21 i3 c2;
  let tmp4,c4 = carry26_wide i4 c3 in
  carry26_wide_fits_lemma #w #13 i4 c3;
  let tmp0',c5 = carry26 tmp0 (vec_smul_mod c4 (u64 5)) in
  vec_smul_mod_fits_lemma #w c4;
  carry26_fits_lemma #w tmp0 (vec_smul_mod c4 (u64 5));
  let tmp1' = vec_add_mod tmp1 c5 in
  acc_inv_lemma #w (tmp0', tmp1, tmp2, tmp3, tmp4) c5

val carry_wide_felem5_eval_lemma_i_0:
    #w:lanes
  -> inp:felem_wide5 w
  -> i:nat{i < w}
  -> Lemma
    (requires felem_wide_fits5 inp (57, 37, 30, 21, 13))
    (ensures
      (let (i0, i1, i2, i3, i4) = inp in
      let tmp0,c0 = carry26_wide i0 (zero w) in
      let tmp1,c1 = carry26_wide i1 c0 in
      let tmp2,c2 = carry26_wide i2 c1 in
      let tmp3,c3 = carry26_wide i3 c2 in
      let tmp4,c4 = carry26_wide i4 c3 in
      let tmp = (tmp0, tmp1, tmp2, tmp3, tmp4) in
      let (t0, t1, t2, t3, t4) = as_tup64_i tmp i in
      let (ti0, ti1, ti2, ti3, ti4) = as_tup64_i inp i in
      let vc0 = (uint64xN_v c0).[i] in
      let vc1 = (uint64xN_v c1).[i] in
      let vc2 = (uint64xN_v c2).[i] in
      let vc3 = (uint64xN_v c3).[i] in
      let vc4 = (uint64xN_v c4).[i] in
      felem_fits1 c4 14 /\
      felem_fits5 tmp (1, 1, 1, 1, 1) /\
      (feval5 inp).[i] ==
	(v t0 + vc4 * 5 + v t1 * pow26 + v t2 * pow26 * pow26 +
	v t3 * pow26 * pow26 * pow26 + v t4 * pow26 * pow26 * pow26 * pow26) % prime))
let carry_wide_felem5_eval_lemma_i_0 #w inp i =
  let (i0, i1, i2, i3, i4) = inp in
  let tmp0,c0 = carry26_wide i0 (zero w) in
  let tmp1,c1 = carry26_wide i1 c0 in
  let tmp2,c2 = carry26_wide i2 c1 in
  let tmp3,c3 = carry26_wide i3 c2 in
  let tmp4,c4 = carry26_wide i4 c3 in

  let tmp = (tmp0, tmp1, tmp2, tmp3, tmp4) in
  let (t0, t1, t2, t3, t4) = as_tup64_i tmp i in
  let (ti0, ti1, ti2, ti3, ti4) = as_tup64_i inp i in
  let vc0 = (uint64xN_v c0).[i] in
  let vc1 = (uint64xN_v c1).[i] in
  let vc2 = (uint64xN_v c2).[i] in
  let vc3 = (uint64xN_v c3).[i] in
  let vc4 = (uint64xN_v c4).[i] in

  carry26_wide_eval_lemma #w #57 i0 (zero w);
  assert ((uint64xN_v i0).[i] ==
    (uint64xN_v c0).[i] * pow2 26 + (uint64xN_v tmp0).[i]);
  carry26_wide_eval_lemma #w #37 i1 c0;
  assert ((uint64xN_v i1).[i] + (uint64xN_v c0).[i] ==
    (uint64xN_v c1).[i] * pow2 26 + (uint64xN_v tmp1).[i]);
  carry26_wide_eval_lemma #w #30 i2 c1;
  assert ((uint64xN_v i2).[i] + (uint64xN_v c1).[i] ==
    (uint64xN_v c2).[i] * pow2 26 + (uint64xN_v tmp2).[i]);
  carry26_wide_eval_lemma #w #21 i3 c2;
  assert ((uint64xN_v i3).[i] + (uint64xN_v c2).[i] ==
    (uint64xN_v c3).[i] * pow2 26 + (uint64xN_v tmp3).[i]);
  carry26_wide_eval_lemma #w #13 i4 c3;
  assert ((uint64xN_v i4).[i] + (uint64xN_v c3).[i] ==
    (uint64xN_v c4).[i] * pow2 26 + (uint64xN_v tmp4).[i]);

  assert ((feval5 inp).[i] ==
    (vc0 * pow2 26 + v t0 + (vc1 * pow2 26 + v t1 - vc0) * pow26 +
    (vc2 * pow2 26 + v t2 - vc1) * pow26 * pow26 +
    (vc3 * pow2 26 + v t3 - vc2) * pow26 * pow26 * pow26 +
    (vc4 * pow2 26 + v t4 - vc3) * pow26 * pow26 * pow26 * pow26) % prime);

  carry_wide_felem5_lemma vc0 vc1 vc2 vc3 vc4 (v t0) (v t1) (v t2) (v t3) (v t4)

val carry_wide_felem5_eval_lemma_i:
    #w:lanes
  -> inp:felem_wide5 w
  -> i:nat{i < w}
  -> Lemma
    (requires felem_wide_fits5 inp (57, 37, 30, 21, 13))
    (ensures (feval5 (carry_wide_felem5 #w inp)).[i] == (feval5 inp).[i])
let carry_wide_felem5_eval_lemma_i #w inp i =
  let (i0, i1, i2, i3, i4) = inp in
  let tmp0,c0 = carry26_wide i0 (zero w) in
  let tmp1,c1 = carry26_wide i1 c0 in
  let tmp2,c2 = carry26_wide i2 c1 in
  let tmp3,c3 = carry26_wide i3 c2 in
  let tmp4,c4 = carry26_wide i4 c3 in
  carry_wide_felem5_eval_lemma_i_0 #w inp i;

  let tmp = (tmp0, tmp1, tmp2, tmp3, tmp4) in
  let (t0, t1, t2, t3, t4) = as_tup64_i tmp i in
  let (ti0, ti1, ti2, ti3, ti4) = as_tup64_i inp i in
  let vc0 = (uint64xN_v c0).[i] in
  let vc1 = (uint64xN_v c1).[i] in
  let vc2 = (uint64xN_v c2).[i] in
  let vc3 = (uint64xN_v c3).[i] in
  let vc4 = (uint64xN_v c4).[i] in
  assert ((feval5 inp).[i] ==
    (v t0 + vc4 * 5 + v t1 * pow26 + v t2 * pow26 * pow26 +
    v t3 * pow26 * pow26 * pow26 + v t4 * pow26 * pow26 * pow26 * pow26) % prime);
  assert (vc4 <= 14 * max26);
  assert (felem_fits5 tmp (1, 1, 1, 1, 1));

  let cin = vec_smul_mod c4 (u64 5) in
  assert ((uint64xN_v cin).[i] == vc4 * 5);
  vec_smul_mod_fits_lemma c4;
  let tmp0', c5 = carry26 tmp0 cin in
  carry26_eval_lemma #w tmp0 cin;
  assert (v t0 + vc4 * 5 == (uint64xN_v c5).[i] * pow2 26 + (uint64xN_v tmp0').[i]);

  let tmp1' = vec_add_mod tmp1 c5 in
  FStar.Math.Lemmas.modulo_lemma ((uint64xN_v tmp1).[i] + (uint64xN_v c5).[i]) (pow2 64);
  assert ((uint64xN_v tmp1').[i] == (uint64xN_v tmp1).[i] + (uint64xN_v c5).[i]);
  let out = (tmp0', tmp1', tmp2, tmp3, tmp4) in
  let (o0, o1, o2, o3, o4) = as_tup64_i out i in
  assert ((feval5 out).[i] ==
    (v o0 + v o1 * pow26 + v t2 * pow26 * pow26 +
     v t3 * pow26 * pow26 * pow26 + v t4 * pow26 * pow26 * pow26 * pow26) % prime);
  assert_norm (pow26 = pow2 26);
  assert ((feval5 out).[i] ==
    (v t0 + vc4 * 5 - (uint64xN_v c5).[i] * pow26 + (v t1 + (uint64xN_v c5).[i]) * pow26 + v t2 * pow26 * pow26 +
     v t3 * pow26 * pow26 * pow26 + v t4 * pow26 * pow26 * pow26 * pow26) % prime);
  FStar.Math.Lemmas.distributivity_add_left (v t1) (uint64xN_v c5).[i] pow26

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

val carry_full_felem5_lemma:
    #w:lanes
  -> f:felem5 w
  -> Lemma
    (requires felem_fits5 f (4, 8, 4, 4, 4))
    (ensures
      acc_inv_t (carry_full_felem5 f) /\
      feval5 (carry_full_felem5 f) == feval5 f)
let carry_full_felem5_lemma #w f =
  assert (felem_wide_fits5 f (57, 37, 30, 21, 13));
  carry_wide_felem5_eval_lemma f;
  carry_wide_felem5_fits_lemma f

val carry_reduce_lemma_i:
    #w:lanes
  -> l:uint64xN w
  -> cin:uint64xN w
  -> i:nat{i < w}
  -> Lemma
    (requires
      (uint64xN_v l).[i] <= 2 * max26 /\
      (uint64xN_v cin).[i] <= 62 * max26)
    (ensures
     (let (l0, l1) = carry26 #w l cin in
      (uint64xN_v l0).[i] <= max26 /\ (uint64xN_v l1).[i] <= 63 /\
      (uint64xN_v l).[i] + (uint64xN_v cin).[i] ==
	(uint64xN_v l1).[i] * pow2 26 + (uint64xN_v l0).[i]))
let carry_reduce_lemma_i #w l cin i =
  let li = (vec_v l).[i] in
  let cini = (vec_v cin).[i] in
  let mask26 = u64 0x3ffffff in
  assert_norm (0x3ffffff = pow2 26 - 1);
  FStar.Math.Lemmas.modulo_lemma (v li + v cini) (pow2 64);
  let li' = li +! cini in
  let li0 = li' &. mask26 in
  let li1 = li' >>. 26ul in
  mod_mask_lemma li' 26ul;
  uintv_extensionality (mod_mask #U64 26ul) mask26;
  FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 (v li') 26 32;
  FStar.Math.Lemmas.pow2_minus 32 26

val carry_reduce_felem5_fits_lemma_i0:
    #w:lanes
  -> f:felem5 w
  -> i:nat{i < w}
  -> Lemma
    (requires acc_inv_t f)
    (ensures
      (let (f0, f1, f2, f3, f4) = f in
      let tmp0,c0 = carry26 f0 (zero w) in
      let tmp1,c1 = carry26 f1 c0 in
      let tmp2,c2 = carry26 f2 c1 in
      let tmp3,c3 = carry26 f3 c2 in
      let tmp4,c4 = carry26 f4 c3 in
      let res = (tmp0, tmp1, tmp2, tmp3, tmp4) in
      (if (uint64xN_v f1).[i] < pow2 26
      then (uint64xN_v tmp1).[i] < pow2 26
      else (uint64xN_v tmp1).[i] <= 74) /\
      (if (uint64xN_v f1).[i] < pow2 26
      then (uint64xN_v c4).[i] = 0
      else (uint64xN_v c4).[i] <= 63) /\
      tup64_fits5 (as_tup64_i res i) (1, 1, 1, 1, 1)))
let carry_reduce_felem5_fits_lemma_i0 #w f i =
  assert_norm (max26 == pow2 26 - 1);
  let (f0, f1, f2, f3, f4) = f in
  let tmp0,c0 = carry26 f0 (zero w) in
  carry_reduce_lemma_i f0 (zero w) i;
  let tmp1,c1 = carry26 f1 c0 in
  carry_reduce_lemma_i f1 c0 i;
  assert (if (uint64xN_v f1).[i] < pow2 26
    then (uint64xN_v tmp1).[i] < pow2 26 else (uint64xN_v tmp1).[i] <= 74);
  let tmp2,c2 = carry26 f2 c1 in
  carry_reduce_lemma_i f2 c1 i;
  let tmp3,c3 = carry26 f3 c2 in
  carry_reduce_lemma_i f3 c2 i;
  let tmp4,c4 = carry26 f4 c3 in
  carry_reduce_lemma_i f4 c3 i;
  let res = (tmp0, tmp1, tmp2, tmp3, tmp4) in
  assert (tup64_fits5 (as_tup64_i res i) (1, 1, 1, 1, 1))

val carry_reduce_felem5_fits_lemma_i:
    #w:lanes
  -> f:felem5 w
  -> i:nat{i < w}
  -> Lemma
    (requires acc_inv_t f)
    (ensures tup64_fits5 (as_tup64_i (carry_full_felem5 f) i) (1, 1, 1, 1, 1))
let carry_reduce_felem5_fits_lemma_i #w f i =
  assert_norm (max26 == pow2 26 - 1);
  let (f0, f1, f2, f3, f4) = f in
  let tmp0,c0 = carry26 f0 (zero w) in
  let tmp1,c1 = carry26 f1 c0 in
  let tmp2,c2 = carry26 f2 c1 in
  let tmp3,c3 = carry26 f3 c2 in
  let tmp4,c4 = carry26 f4 c3 in
  carry_reduce_felem5_fits_lemma_i0 #w f i;
  FStar.Math.Lemmas.modulo_lemma ((uint64xN_v c4).[i] * 5) (pow2 64);
  assert ((uint64xN_v (vec_smul_mod c4 (u64 5))).[i] == (uint64xN_v c4).[i] * 5);
  let tmp0',c5 = carry26 tmp0 (vec_smul_mod c4 (u64 5)) in
  carry_reduce_lemma_i tmp0 (vec_smul_mod c4 (u64 5)) i;
  assert (if (uint64xN_v f1).[i] < pow2 26 then (uint64xN_v c5).[i] = 0 else (uint64xN_v c5).[i] <= 63);
  let tmp1' = vec_add_mod tmp1 c5 in
  let res = (tmp0', tmp1', tmp2, tmp3, tmp4) in
  assert (tup64_fits5 (as_tup64_i res i) (1, 1, 1, 1, 1))

val carry_reduce_felem5_fits_lemma:
    #w:lanes
  -> f:felem5 w
  -> Lemma
    (requires acc_inv_t f)
    (ensures felem_fits5 (carry_full_felem5 f) (1, 1, 1, 1, 1))
let carry_reduce_felem5_fits_lemma #w f =
  match w with
  | 1 ->
    carry_reduce_felem5_fits_lemma_i #w f 0
  | 2 ->
    carry_reduce_felem5_fits_lemma_i #w f 0;
    carry_reduce_felem5_fits_lemma_i #w f 1
  | 4 ->
    carry_reduce_felem5_fits_lemma_i #w f 0;
    carry_reduce_felem5_fits_lemma_i #w f 1;
    carry_reduce_felem5_fits_lemma_i #w f 2;
    carry_reduce_felem5_fits_lemma_i #w f 3

val carry_reduce_felem5_lemma:
    #w:lanes
  -> f:felem5 w
  -> Lemma
    (requires acc_inv_t f)
    (ensures
      felem_fits5 (carry_full_felem5 f) (1, 1, 1, 1, 1) /\
      feval5 (carry_full_felem5 f) == feval5 f)
let carry_reduce_felem5_lemma #w f =
  carry_reduce_felem5_fits_lemma #w f;
  assert (felem_wide_fits5 f (57, 37, 30, 21, 13));
  carry_wide_felem5_eval_lemma f


val lemma_subtract_p5_0:
    f:tup64_5{tup64_fits5 f (1, 1, 1, 1, 1)}
  -> f':tup64_5
  -> Lemma
    (requires
      (let (f0, f1, f2, f3, f4) = f in
      let (f0', f1', f2', f3', f4') = f' in
      (v f4 <> 0x3ffffff || v f3 <> 0x3ffffff || v f2 <> 0x3ffffff || v f1 <> 0x3ffffff || v f0 < 0x3fffffb) /\
      (v f0' = v f0 && v f1' = v f1 && v f2' = v f2 && v f3' = v f3 && v f4' = v f4)))
    (ensures as_nat5 f' == as_nat5 f % prime)
let lemma_subtract_p5_0 f f' =
  let (f0, f1, f2, f3, f4) = f in
  let (f0', f1', f2', f3', f4') = f' in
  assert_norm (max26 = pow2 26 - 1);
  assert_norm (0x3ffffff = max26);
  assert_norm (0x3fffffb = max26 - 4);
  assert (as_nat5 f == v f0 + v f1 * pow26 + v f2 * pow26 * pow26 +
    v f3 * pow26 * pow26 * pow26 + v f4 * pow26 * pow26 * pow26 * pow26);
  assert (as_nat5 f <= pow26 - 5 + (pow2 26 - 1) * pow26 + (pow2 26 - 1) * pow26 * pow26 +
    (pow2 26 - 1) * pow26 * pow26 * pow26 + (pow2 26 - 1) * pow26 * pow26 * pow26 * pow26);
  assert_norm (pow2 26 * pow26 * pow26 * pow26 * pow26 = pow2 130);
  assert (as_nat5 f < pow2 130 - 5);
  assert (as_nat5 f == as_nat5 f');
  FStar.Math.Lemmas.modulo_lemma (as_nat5 f') prime

val lemma_subtract_p5_1:
    f:tup64_5{tup64_fits5 f (1, 1, 1, 1, 1)}
  -> f':tup64_5
  -> Lemma
    (requires
      (let (f0, f1, f2, f3, f4) = f in
      let (f0', f1', f2', f3', f4') = f' in
      (v f4 = 0x3ffffff && v f3 = 0x3ffffff && v f2 = 0x3ffffff && v f1 = 0x3ffffff && v f0 >= 0x3fffffb) /\
      (v f0' = v f0 - 0x3fffffb && v f1' = v f1 - 0x3ffffff && v f2' = v f2 - 0x3ffffff &&
	v f3' = v f3 - 0x3ffffff && v f4' = v f4 - 0x3ffffff)))
    (ensures as_nat5 f' == as_nat5 f % prime)
let lemma_subtract_p5_1 f f' =
  let (f0, f1, f2, f3, f4) = f in
  let (f0', f1', f2', f3', f4') = f' in
  assert_norm (max26 = pow2 26 - 1);
  assert_norm (0x3ffffff = max26);
  assert_norm (0x3fffffb = max26 - 4);
  assert (as_nat5 f' % prime ==
    (v f0' + v f1' * pow26 + v f2' * pow26 * pow26 +
     v f3' * pow26 * pow26 * pow26 + v f4' * pow26 * pow26 * pow26 * pow26) % prime);
  assert (as_nat5 f' % prime ==
    (v f0 - (pow2 26 - 5) + (v f1 - (pow2 26 - 1)) * pow26 + (v f2 - (pow2 26 - 1)) * pow26 * pow26 +
    (v f3 - (pow2 26 - 1)) * pow26 * pow26 * pow26 + (v f4 - (pow2 26 - 1)) * pow26 * pow26 * pow26 * pow26) % prime);
  assert_norm (pow2 26 * pow26 * pow26 * pow26 * pow26 = pow2 130);
  assert (as_nat5 f' % prime ==
    (v f0 + v f1 * pow2 26 + v f2 * pow26 * pow26 +
    v f3 * pow26 * pow26 * pow26 +
    v f4 * pow26 * pow26 * pow26 * pow26 - prime) % prime);
  FStar.Math.Lemmas.lemma_mod_sub
    (v f0 + v f1 * pow2 26 + v f2 * pow26 * pow26 +
    v f3 * pow26 * pow26 * pow26 + v f4 * pow26 * pow26 * pow26 * pow26) 1 prime

val lemma_subtract_p5:
    f:tup64_5{tup64_fits5 f (1, 1, 1, 1, 1)}
  -> f':tup64_5
  -> Lemma
    (requires
      (let (f0, f1, f2, f3, f4) = f in
      let (f0', f1', f2', f3', f4') = f' in
      ((v f4 = 0x3ffffff && v f3 = 0x3ffffff && v f2 = 0x3ffffff && v f1 = 0x3ffffff && v f0 >= 0x3fffffb) /\
      (v f0' = v f0 - 0x3fffffb && v f1' = v f1 - 0x3ffffff && v f2' = v f2 - 0x3ffffff &&
	v f3' = v f3 - 0x3ffffff && v f4' = v f4 - 0x3ffffff)) \/
      ((v f4 <> 0x3ffffff || v f3 <> 0x3ffffff || v f2 <> 0x3ffffff || v f1 <> 0x3ffffff || v f0 < 0x3fffffb) /\
      (v f0' = v f0 && v f1' = v f1 && v f2' = v f2 && v f3' = v f3 && v f4' = v f4))))
    (ensures as_nat5 f' == as_nat5 f % prime)
let lemma_subtract_p5 f f' =
  let (f0, f1, f2, f3, f4) = f in
  let (f0', f1', f2', f3', f4') = f' in
  assert_norm (max26 = pow2 26 - 1);
  if ((v f4 <> 0x3ffffff || v f3 <> 0x3ffffff || v f2 <> 0x3ffffff || v f1 <> 0x3ffffff || v f0 < 0x3fffffb) &&
     (v f0' = v f0 && v f1' = v f1 && v f2' = v f2 && v f3' = v f3 && v f4' = v f4))
  then lemma_subtract_p5_0 f f'
  else lemma_subtract_p5_1 f f'

inline_for_extraction
val subtract_p5_s:
    #w:lanes
  -> f:felem5 w{felem_fits5 f (1, 1, 1, 1, 1)}
  -> i:nat{i < w}
  -> Pure tup64_5
    (requires True)
    (ensures (fun out ->
      tup64_fits5 out (1, 1, 1, 1, 1) /\
      as_nat5 out == as_nat5 (as_tup64_i f i) % prime))
let subtract_p5_s #w f i =
  let (f0, f1, f2, f3, f4) = as_tup64_i f i in
  let mask0 = eq_mask f4 (u64 0x3ffffff) in
  let mask1 = mask0 &. eq_mask f3 (u64 0x3ffffff) in
  let mask2 = mask1 &. eq_mask f2 (u64 0x3ffffff) in
  let mask3 = mask2 &. eq_mask f1 (u64 0x3ffffff) in
  let mask4 = mask3 &. gte_mask f0 (u64 0x3fffffb) in

  let p0 = mask4 &. u64 0x3fffffb in
  logand_lemma mask4 (u64 0x3fffffb);
  let p1 = mask4 &. u64 0x3ffffff in
  logand_lemma mask4 (u64 0x3ffffff);
  let p2 = mask4 &. u64 0x3ffffff in
  let p3 = mask4 &. u64 0x3ffffff in
  let p4 = mask4 &. u64 0x3ffffff in

  let f0' = f0 -. p0 in
  let f1' = f1 -. p1 in
  let f2' = f2 -. p2 in
  let f3' = f3 -. p3 in
  let f4' = f4 -. p4 in
  lemma_subtract_p5 (f0, f1, f2, f3, f4) (f0', f1', f2', f3', f4');
  (f0', f1', f2', f3', f4')

#push-options "--max_ifuel 1"
val subtract_p5_felem5_lemma_i:
    #w:lanes
  -> f:felem5 w{felem_fits5 f (1, 1, 1, 1, 1)}
  -> i:nat{i < w}
  -> Lemma (
      tup64_fits5 (as_tup64_i (subtract_p5 #w f) i) (1, 1, 1, 1, 1) /\
      as_nat5 (as_tup64_i (subtract_p5 #w f) i) == as_nat5 (as_tup64_i f i) % prime)
let subtract_p5_felem5_lemma_i #w f i =
  assert (subtract_p5_s #w f i == as_tup64_i (subtract_p5 #w f) i)
#pop-options

val subtract_p5_felem5_lemma:
    #w:lanes
  -> f:felem5 w
  -> Lemma
    (requires felem_fits5 f (1, 1, 1, 1, 1))
    (ensures
      felem_fits5 (subtract_p5 f) (1, 1, 1, 1, 1) /\
      (fas_nat5 (subtract_p5 f)).[0] == (feval5 f).[0])
let subtract_p5_felem5_lemma #w f =
  match w with
  | 1 ->
    subtract_p5_felem5_lemma_i #w f 0
  | 2 ->
    subtract_p5_felem5_lemma_i #w f 0;
    subtract_p5_felem5_lemma_i #w f 1
  | 4 ->
    subtract_p5_felem5_lemma_i #w f 0;
    subtract_p5_felem5_lemma_i #w f 1;
    subtract_p5_felem5_lemma_i #w f 2;
    subtract_p5_felem5_lemma_i #w f 3


val load_tup64_lemma0_lo: lo:uint64 ->
  Lemma
    (v lo % pow2 26 + ((v lo / pow2 26) % pow2 26) * pow26 +
    v lo / pow2 52 * pow26 * pow26 == v lo)
let load_tup64_lemma0_lo lo =
  assert_norm (pow26 = pow2 26);
  assert_norm (pow26 * pow26 = pow2 52);
  FStar.Math.Lemmas.pow2_modulo_division_lemma_1 (v lo) 26 52;
  assert (v lo % pow2 26 == (v lo % pow2 52) % pow2 26);
  FStar.Math.Lemmas.euclidean_division_definition (v lo % pow2 52) (pow2 26);
  FStar.Math.Lemmas.euclidean_division_definition (v lo) (pow2 52)

val load_tup64_lemma0_hi: hi:uint64 ->
  Lemma
    (v hi % pow2 14 + ((v hi / pow2 14) % pow2 26) * pow2 14 +
    (v hi / pow2 40) * pow2 40 == v hi)
let load_tup64_lemma0_hi hi =
  FStar.Math.Lemmas.pow2_modulo_division_lemma_1 (v hi) 14 40;
  FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 (v hi) 14 40;
  assert (v hi % pow2 14 == (v hi % pow2 40) % pow2 14);
  FStar.Math.Lemmas.euclidean_division_definition (v hi % pow2 40) (pow2 14);
  FStar.Math.Lemmas.euclidean_division_definition (v hi) (pow2 40)

val load_tup64_lemma0:
    f:tup64_5
  -> lo:uint64
  -> hi:uint64
  -> Lemma
    (requires (
      let (f0, f1, f2, f3, f4) = f in
      v f0 == v lo % pow2 26 /\
      v f1 == (v lo / pow2 26) % pow2 26 /\
      v f2 == v lo / pow2 52 + (v hi % pow2 14) * pow2 12 /\
      v f3 == (v hi / pow2 14) % pow2 26 /\
      v f4 == v hi / pow2 40))
    (ensures as_nat5 f == v hi * pow2 64 + v lo)
let load_tup64_lemma0 f lo hi =
  let (f0, f1, f2, f3, f4) = f in
  assert_norm (pow26 = pow2 26);
  assert_norm (pow2 12 * pow26 * pow26 = pow2 64);
  assert_norm (pow26 * pow26 * pow26 = pow2 14 * pow2 64);
  assert_norm (pow26 * pow26 * pow26 * pow26 = pow2 40 * pow2 64);
  assert (as_nat5 f ==
    v lo % pow2 26 + ((v lo / pow2 26) % pow2 26) * pow26 +
    v lo / pow2 52 * pow26 * pow26 + (v hi % pow2 14) * pow2 64 +
    ((v hi / pow2 14) % pow2 26) * pow2 14 * pow2 64 +
    (v hi / pow2 40) * pow2 40 * pow2 64);
  assert (as_nat5 f ==
    v lo % pow2 26 + ((v lo / pow2 26) % pow2 26) * pow26 +
    v lo / pow2 52 * pow26 * pow26 + (v hi % pow2 14 +
    ((v hi / pow2 14) % pow2 26) * pow2 14 +
    (v hi / pow2 40) * pow2 40) * pow2 64);
  load_tup64_lemma0_lo lo;
  load_tup64_lemma0_hi hi

val load_tup64_fits_lemma:
    f:tup64_5
  -> lo:uint64
  -> hi:uint64
  -> Lemma
    (requires (
      let (f0, f1, f2, f3, f4) = f in
      v f0 == v lo % pow2 26 /\
      v f1 == (v lo / pow2 26) % pow2 26 /\
      v f2 == v lo / pow2 52 + (v hi % pow2 14) * pow2 12 /\
      v f3 == (v hi / pow2 14) % pow2 26 /\
      v f4 == v hi / pow2 40))
    (ensures tup64_fits5 f (1, 1, 1, 1, 1))
let load_tup64_fits_lemma f lo hi =
  let (f0, f1, f2, f3, f4) = f in
  assert_norm (pow26 = pow2 26);
  FStar.Math.Lemmas.lemma_div_lt_nat (v lo) 64 52;
  lemma_mult_le (v hi % pow2 14) (pow2 14 - 1) (pow2 12) (pow2 12);
  assert_norm (pow2 14 * pow2 12 = pow2 26);
  FStar.Math.Lemmas.lemma_div_lt_nat (v hi) 64 40;
  assert_norm (pow2 24 < pow2 26)

val load_tup64_lemma:
    lo:uint64
  -> hi:uint64
  -> Pure tup64_5
    (requires True)
    (ensures (fun f ->
      tup64_fits5 f (1, 1, 1, 1, 1) /\
      as_nat5 f < pow2 128 /\
      as_nat5 f % prime == v hi * pow2 64 + v lo))

let load_tup64_lemma lo hi =
  let mask26 = u64 0x3ffffff in
  assert_norm (0x3ffffff = pow2 26 - 1);
  assert_norm (0x3fff = pow2 14 - 1);

  let f0 = lo &. mask26 in
  mod_mask_lemma lo 26ul;
  uintv_extensionality (mod_mask #U64 26ul) mask26;
  assert (v f0 == v lo % pow2 26);

  let f1 = (lo >>. 26ul) &. mask26 in
  assert (v f1 == (v lo / pow2 26) % pow2 26);

  let f2 = (lo >>. 52ul) |. ((hi &. u64 0x3fff) <<. 12ul) in
  FStar.Math.Lemmas.lemma_div_lt (v lo) 64 52;
  mod_mask_lemma hi 14ul;
  uintv_extensionality (mod_mask #U64 14ul) (u64 0x3fff);
  FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_1 (v hi % pow2 14) 12 12;
  assert ((v (lo >>. 52ul)) < pow2 12);
  [@inline_let] let tmp = (hi &. u64 0x3fff) in
  calc (==) {
    v (tmp <<. 12ul) % pow2 12;
  (==) { shift_left_lemma (hi &. u64 0x3fff) 12ul }
    (v tmp * pow2 12 % pow2 64) % pow2 12;
  (==) { assert_norm (pow2 64 = pow2 12 * pow2 52) }
    (v tmp * pow2 12 % (pow2 12 * pow2 52)) % pow2 12;
  (==) {FStar.Math.Lemmas.modulo_modulo_lemma (v tmp * pow2 12) (pow2 12) (pow2 52)}
    v tmp * pow2 12 % pow2 12;
  (==) {FStar.Math.Lemmas.multiple_modulo_lemma (v (hi &. u64 0x3fff)) 12}
    0;
  };
  assert_norm (12 < pow2 (bits U64));
  logor_disjoint (lo >>. 52ul) ((hi &. u64 0x3fff) <<. 12ul) 12;
  calc (==) {
    v f2;
  (==) {  }
    v (lo >>. 52ul) + v ((hi &. u64 0x3fff) <<. 12ul);
  (==) { shift_right_lemma lo 52ul }
    v lo / pow2 52 + v ((hi &. u64 0x3fff) <<. 12ul);
  (==) { shift_left_lemma (hi &. u64 0x3fff) 12ul }
    v lo / pow2 52 + v (hi &. u64 0x3fff) * pow2 12 % pow2 64;
  (==) { mod_mask_lemma hi 14ul }
    v lo / pow2 52 + (v hi % pow2 14) * pow2 12 % pow2 64;
  };
  assert (v hi % pow2 14 < pow2 14);
  assert_norm (pow2 14 * pow2 12 < pow2 64);
  FStar.Math.Lemmas.small_modulo_lemma_1 ((v hi % pow2 14) * pow2 12) (pow2 64);
  assert (v f2 == v lo / pow2 52 + (v hi % pow2 14) * pow2 12);

  let f3 = (hi >>. 14ul) &. mask26 in
  assert (v f3 == (v hi / pow2 14) % pow2 26);

  let f4 = hi >>. 40ul in
  assert (v f4 == v hi / pow2 40);
  let f = (f0, f1, f2, f3, f4) in
  load_tup64_lemma0 f lo hi;
  load_tup64_fits_lemma f lo hi;
  assert (as_nat5 f < pow2 128);
  assert_norm (pow2 128 < prime);
  FStar.Math.Lemmas.small_modulo_lemma_1 (as_nat5 f) prime;
  assert (as_nat5 f % prime == v hi * pow2 64 + v lo);
  f

val load_felem5_lemma_i:
    #w:lanes
  -> lo:uint64xN w
  -> hi:uint64xN w
  -> i:nat{i < w}
  -> Lemma
    (let f = as_tup64_i (load_felem5 #w lo hi) i in
    tup64_fits5 f (1, 1, 1, 1, 1) /\
    as_nat5 f < pow2 128 /\
    as_nat5 f % prime == (uint64xN_v hi).[i] * pow2 64 + (uint64xN_v lo).[i])
let load_felem5_lemma_i #w lo hi i =
  assert (as_tup64_i (load_felem5 #w lo hi) i == load_tup64_lemma (vec_v lo).[i] (vec_v hi).[i])

val lemma_store_felem_lo: f:tup64_5 -> lo:uint64 ->
  Lemma
    (requires tup64_fits5 f (1, 1, 1, 1, 1))
    (ensures
     (let (f0, f1, f2, f3, f4) = f in
     let lo = f0 |. (f1 <<. 26ul) |. (f2 <<. 52ul) in
     v lo == v f0 + v f1 * pow2 26 + (v f2 * pow2 52) % pow2 64))
let lemma_store_felem_lo f lo =
  let (f0, f1, f2, f3, f4) = f in
  assert_norm (max26 = pow2 26 - 1);
  let lo = f0 |. (f1 <<. 26ul) |. (f2 <<. 52ul) in
  FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_1 (v f1) 26 26;
  logor_disjoint f0 (f1 <<. 26ul) 26;
  assert (v (f0 |. (f1 <<. 26ul)) == v f0 + v f1 * pow2 26);
  assert_norm (pow2 26 * pow2 26 = pow2 52);
  assert (v f0 + v f1 * pow2 26 < pow2 52);
  assert (((v f2 * pow2 52) % pow2 64) % pow2 52 = 0);
  logor_disjoint (f0 |. (f1 <<. 26ul)) (f2 <<. 52ul) 52

val lemma_store_felem_hi: f:tup64_5 -> hi:uint64 ->
  Lemma
    (requires tup64_fits5 f (1, 1, 1, 1, 1))
    (ensures
     (let (f0, f1, f2, f3, f4) = f in
     let hi = (f2 >>. 12ul) |. (f3 <<. 14ul) |. (f4 <<. 40ul) in
     v hi == v f2 / pow2 12 + v f3 * pow2 14 + (v f4 * pow2 40) % pow2 64))
let lemma_store_felem_hi f hi =
  let (f0, f1, f2, f3, f4) = f in
  assert_norm (max26 = pow2 26 - 1);
  let hi = (f2 >>. 12ul) |. (f3 <<. 14ul) |. (f4 <<. 40ul) in
  FStar.Math.Lemmas.lemma_div_lt (v f2) 26 12;
  assert (v f2 / pow2 12 < pow2 14);
  assert_norm (pow2 26 * pow2 14 = pow2 40);
  assert_norm (pow2 40 < pow2 64);
  FStar.Math.Lemmas.modulo_lemma (v f3 * pow2 14) (pow2 64);
  FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_1 (v f3) 14 14;
  assert ((v f3 * pow2 14) % pow2 14 = 0);
  logor_disjoint (f2 >>. 12ul) (f3 <<. 14ul) 14;
  assert (v ((f2 >>. 12ul) |. (f3 <<. 14ul)) == v f2 / pow2 12 + v f3 * pow2 14);
  FStar.Math.Lemmas.lemma_mult_le_right (pow2 14) (v f3) (pow2 26 - 1);
  assert (v f2 / pow2 12 + v f3 * pow2 14 < pow2 40);
  FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 (v f4 * pow2 40) 40 64;
  //assert (((v f4 * pow2 40) % pow2 64) % pow2 40 = (v f4 * pow2 40) % pow2 40);
  FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_1 (v f4) 40 40;
  //assert ((v f4 * pow2 40) % pow2 40 = 0);
  logor_disjoint ((f2 >>. 12ul) |. (f3 <<. 14ul)) (f4 <<. 40ul) 40

val lemma_tup64_mod_pow2_128: f:tup64_5 ->
  Lemma
  (requires tup64_fits5 f (1, 1, 1, 1, 1))
  (ensures (
    let (f0, f1, f2, f3, f4) = f in
    (as_nat5 f) % pow2 128 ==
    v f0 + v f1 * pow26 + v f2 * pow26 * pow26 +
    v f3 * pow26 * pow26 * pow26 + (v f4 % pow2 24) * pow26 * pow26 * pow26 * pow26))
let lemma_tup64_mod_pow2_128 f =
  let (f0, f1, f2, f3, f4) = f in
  assert ((as_nat5 f) % pow2 128 ==
   (v f0 + v f1 * pow26 + v f2 * pow26 * pow26 +
    v f3 * pow26 * pow26 * pow26 + v f4 * pow26 * pow26 * pow26 * pow26) % pow2 128);
  FStar.Math.Lemmas.lemma_mod_plus_distr_r (v f0 + v f1 * pow26 + v f2 * pow26 * pow26 +
    v f3 * pow26 * pow26 * pow26) (v f4 * pow26 * pow26 * pow26 * pow26) (pow2 128);
  assert_norm (pow26 = pow2 26);
  assert_norm (pow2 26 * pow2 26 * pow2 26 * pow2 26 = pow2 104);
  assert ((v f4 * pow26 * pow26 * pow26 * pow26) % pow2 128 = (v f4 * pow2 104) % pow2 128);
  FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v f4) 128 104;
  assert ((v f4 * pow26 * pow26 * pow26 * pow26) % pow2 128 = (v f4 % pow2 24) * pow2 104);
  assert ((as_nat5 f) % pow2 128 ==
   (v f0 + v f1 * pow26 + v f2 * pow26 * pow26 +
    v f3 * pow26 * pow26 * pow26 + (v f4 % pow2 24) * pow26 * pow26 * pow26 * pow26) % pow2 128);

  let f4' = u64 (v f4 % pow2 24) in
  let f' = (f0, f1, f2, f3, f4') in
  assert (as_nat5 f' <= pow2 26 - 1 + (pow2 26 - 1) * pow26 +
    (pow2 26 - 1) * pow26 * pow26 + (pow2 26 - 1) * pow26 * pow26 * pow26 +
    (pow2 24 - 1) * pow26 * pow26 * pow26 * pow26);
  assert (as_nat5 f' <= pow2 24 * pow26 * pow26 * pow26 * pow26 - 1);
  assert_norm (pow2 24 * pow2 26 * pow2 26 * pow2 26 * pow2 26 = pow2 128);
  assert (as_nat5 f' < pow2 128);
  FStar.Math.Lemmas.modulo_lemma (as_nat5 f') (pow2 128)

val lemma_tup64_as_nat: f:tup64_5 ->
  Lemma (
    let (f0, f1, f2, f3, f4) = f in
    as_nat5 f == v f0 + v f1 * pow2 26 +
      v f2 * pow2 52 + v f3 * pow2 78 + v f4 * pow2 104)
let lemma_tup64_as_nat f =
  let (f0, f1, f2, f3, f4) = f in
  assert (as_nat5 f == v f0 + v f1 * pow26 + v f2 * pow26 * pow26 +
    v f3 * pow26 * pow26 * pow26 + v f4 * pow26 * pow26 * pow26 * pow26);
  assert_norm (pow26 = pow2 26);
  assert_norm (pow2 26 * pow2 26 = pow2 52);
  assert_norm (pow2 26 * pow2 26 * pow2 26 = pow2 78);
  assert_norm (pow2 26 * pow2 26 * pow2 26 * pow2 26 = pow2 104)

val store_tup64_lemma:
    f:tup64_5
  -> Pure (uint64 & uint64)
    (requires tup64_fits5 f (1, 1, 1, 1, 1))
    (ensures (fun (lo, hi) -> v hi * pow2 64 + v lo == as_nat5 f % pow2 128))
let store_tup64_lemma f =
  let (f0, f1, f2, f3, f4) = f in
  let lo = f0 |. (f1 <<. 26ul) |. (f2 <<. 52ul) in
  let hi = (f2 >>. 12ul) |. (f3 <<. 14ul) |. (f4 <<. 40ul) in
  lemma_store_felem_lo f lo;
  lemma_store_felem_hi f hi;

  assert (v lo == v f0 + v f1 * pow2 26 + (v f2 * pow2 52) % pow2 64);
  assert (v hi == v f2 / pow2 12 + v f3 * pow2 14 + (v f4 * pow2 40) % pow2 64);

  assert (v lo + v hi * pow2 64 ==
    v f0 + v f1 * pow2 26 + (v f2 * pow2 52) % pow2 64 +
    (v f2 / pow2 12 + v f3 * pow2 14 + (v f4 * pow2 40) % pow2 64) * pow2 64);
  assert (v lo + v hi * pow2 64 ==
    v f0 + v f1 * pow2 26 + (v f2 * pow2 52) % pow2 64 +
    v f2 / pow2 12 * pow2 64 + v f3 * pow2 14 * pow2 64 + (v f4 * pow2 40) % pow2 64 * pow2 64);
  FStar.Math.Lemmas.multiple_division_lemma (v f2) (pow2 52);
  assert (v f2 == v f2 * pow2 52 / pow2 52);
  assert ((v f2 * pow2 52) % pow2 64 + v f2 / pow2 12 * pow2 64 ==
    (v f2 * pow2 52) % pow2 64 + (v f2 * pow2 52 / pow2 52) / pow2 12 * pow2 64);
  FStar.Math.Lemmas.division_multiplication_lemma  (v f2 * pow2 52) (pow2 52) (pow2 12);
  assert_norm (pow2 52 * pow2 12 = pow2 64);
  assert ((v f2 * pow2 52) % pow2 64 + v f2 / pow2 12 * pow2 64 ==
    (v f2 * pow2 52) % pow2 64 + v f2 * pow2 52 / pow2 64 * pow2 64);
  FStar.Math.Lemmas.euclidean_division_definition (v f2 * pow2 52) (pow2 64);
  assert (v lo + v hi * pow2 64 ==
    v f0 + v f1 * pow2 26 + v f2 * pow2 52 +
    v f3 * pow2 14 * pow2 64 + (v f4 * pow2 40) % pow2 64 * pow2 64);
  FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v f4) 64 40;
  assert (v lo + v hi * pow2 64 ==
    v f0 + v f1 * pow2 26 + v f2 * pow2 52 +
    v f3 * pow2 14 * pow2 64 + (v f4 % pow2 24) * pow2 40 * pow2 64);
  lemma_mul_assos_3 (v f3) (pow2 14) (pow2 64);
  lemma_mul_assos_3 (v f4 % pow2 24) (pow2 40) (pow2 64);
  assert_norm (pow2 40 * pow2 64 = pow2 104);
  assert_norm (pow2 14 * pow2 64 = pow2 78);
  assert (v lo + v hi * pow2 64 ==
    v f0 + v f1 * pow2 26 + v f2 * pow2 52 +
    v f3 * pow2 78 + (v f4 % pow2 24) * pow2 104);
  lemma_tup64_mod_pow2_128 f;
  lemma_tup64_as_nat (f0, f1, f2, f3, u64 (v f4 % pow2 24));
  lo, hi

val store_felem5_lemma_i:
    #w:lanes
  -> f:felem5 w
  -> i:nat{i < w}
  -> Lemma
    (requires felem_fits5 f (1, 1, 1, 1, 1))
    (ensures
      (let (lo, hi) = store_felem5 f in
      (uint64xN_v hi).[i] * pow2 64 + (uint64xN_v lo).[i] == (fas_nat5 f).[i] % pow2 128))
#push-options "--max_ifuel 1"
let store_felem5_lemma_i #w f i =
  let (lo, hi) = store_felem5 f in
  let loi = (vec_v lo).[i] in
  let hii = (vec_v hi).[i] in
  assert (store_tup64_lemma (as_tup64_i f i) == (loi, hii))
#pop-options

#push-options "--z3rlimit 200"
#push-options "--max_ifuel 1"

val lset_bit5_lemma0:
    f:lseq uint64 5
  -> i:size_nat{i <= 128}
  -> Lemma
    (requires
      (forall (i:nat). i < 5 ==> v f.[i] <= max26) /\
      as_nat5 (f.[0], f.[1], f.[2], f.[3], f.[4]) < pow2 i)
    (ensures v f.[i / 26] < pow2 (i % 26))
let lset_bit5_lemma0 f i =
  let j = i % 26 in
  let ind = i / 26 in
  let (f0, f1, f2, f3, f4) = (f.[0], f.[1], f.[2], f.[3], f.[4]) in
  let tf = (f0, f1, f2, f3, f4) in
  assert (as_nat5 tf ==
    v f0 + v f1 * pow26 + v f2 * pow26 * pow26 +
    v f3 * pow26 * pow26 * pow26 + v f4 * pow26 * pow26 * pow26 * pow26);
  assert_norm (pow26 = pow2 26);
  FStar.Math.Lemmas.euclidean_division_definition i 26;
  assert (i == ind * 26 + j);
  match ind with
  | 0 -> ()
  | 1 ->
    assert (v f1 * pow2 26 < pow2 i);
    FStar.Math.Lemmas.lemma_div_lt_nat (v f1 * pow2 26) i 26;
    assert (v f1 < pow2 (i - 26));
    assert (i - 26 == j)
  | 2 ->
    assert (v f2 * pow2 26 * pow2 26 < pow2 i);
    FStar.Math.Lemmas.paren_mul_right (v f2) (pow2 26) (pow2 26);
    assert_norm (pow2 26 * pow2 26 = pow2 52);
    FStar.Math.Lemmas.lemma_div_lt_nat (v f2 * pow2 52) i 52;
    assert (v f2 < pow2 (i - 52));
    assert (i - 52 == j)
  | 3 ->
    assert (78 <= i /\ i < 104);
    let b3 = v f3 * pow2 26 * pow2 26 * pow2 26 in
    lemma_mul_assos_4 (v f3) (pow2 26) (pow2 26) (pow2 26);
    assert_norm (pow2 26 * pow2 26 * pow2 26 = pow2 78);
    FStar.Math.Lemmas.lemma_div_lt_nat (v f3 * pow2 78) i 78;
    assert (v f3 < pow2 (i - 78));
    assert (i - 78 == j)
  | 4 ->
    assert (v f4 * pow2 26 * pow2 26 * pow2 26 * pow2 26 < pow2 i);
    lemma_mul_assos_5 (v f4) (pow2 26) (pow2 26) (pow2 26) (pow2 26);
    assert_norm (pow2 26 * pow2 26 * pow2 26 * pow2 26 = pow2 104);
    assert (v f4 * pow2 104 < pow2 i);
    FStar.Math.Lemmas.lemma_div_lt_nat (v f4 * pow2 104) i 104;
    assert (v f4 < pow2 (i - 104));
    assert (i - 104 == j)
#pop-options

val lset_bit5_lemma1_:
    f:lseq uint64 5
  -> i:size_nat{i <= 128}
  -> Lemma
    (requires
      (forall (i:nat). i < 5 ==> v f.[i] <= max26) /\
      v f.[i / 26] + pow2 (i % 26) <= max26)
    (ensures (
      let fi = u64 (v f.[i / 26] + pow2 (i % 26)) in
      let out = f.[i / 26] <- fi in
      let f1 = (f.[0], f.[1], f.[2], f.[3], f.[4]) in
      let out1 = (out.[0], out.[1], out.[2], out.[3], out.[4]) in
      as_nat5 out1 == pow2 i + as_nat5 f1))
let lset_bit5_lemma1_ f i =
  let fi = u64 (v f.[i / 26] + pow2 (i % 26)) in
  let out = f.[i / 26] <- fi in
  let (f0, f1, f2, f3, f4) = (f.[0], f.[1], f.[2], f.[3], f.[4]) in
  let (o0, o1, o2, o3, o4) = (out.[0], out.[1], out.[2], out.[3], out.[4]) in
  let tf = (f0, f1, f2, f3, f4) in
  let to = (o0, o1, o2, o3, o4) in
  assert_norm (pow26 = pow2 26);
  assert (as_nat5 to == v o0 + v o1 * pow26 + v o2 * pow26 * pow26 +
    v o3 * pow26 * pow26 * pow26 + v o4 * pow26 * pow26 * pow26 * pow26);
  let ind = i / 26 in
  let j = i % 26 in
  assert (i == ind * 26 + j);
  match ind with
  | 0 -> ()
  | 1 ->
    assert (as_nat5 to ==
      v f0 + (v f1 + pow2 j) * pow26 + v f2 * pow26 * pow26 +
      v f3 * pow26 * pow26 * pow26 + v f4 * pow26 * pow26 * pow26 * pow26);
    assert (as_nat5 to == as_nat5 tf + pow2 j * pow26);
    FStar.Math.Lemmas.pow2_plus j 26
  | 2 ->
    assert (as_nat5 to == v f0 + v f1 * pow26 + (v f2 + pow2 j) * pow26 * pow26 +
      v f3 * pow26 * pow26 * pow26 + v f4 * pow26 * pow26 * pow26 * pow26);
    assert (as_nat5 to == as_nat5 tf + pow2 j * pow26 * pow26);
    lemma_mul_assos_3 (pow2 j) pow26 pow26;
    assert_norm (pow2 26 * pow2 26 = pow2 52);
    FStar.Math.Lemmas.pow2_plus j 52
  | 3 ->
    assert (as_nat5 to == v f0 + v f1 * pow26 + v f2 * pow26 * pow26 +
      (v f3 + pow2 j) * pow26 * pow26 * pow26 + v f4 * pow26 * pow26 * pow26 * pow26);
    assert (as_nat5 to == as_nat5 tf + pow2 j * pow26 * pow26 * pow26);
    lemma_mul_assos_4 (pow2 j) pow26 pow26 pow26;
    assert_norm (pow2 26 * pow2 26 * pow2 26 = pow2 78);
    FStar.Math.Lemmas.pow2_plus j 78
  | 4 ->
    assert (as_nat5 to == v f0 + v f1 * pow26 + v f2 * pow26 * pow26 +
      v f3 * pow26 * pow26 * pow26 + (v f4 + pow2 j) * pow26 * pow26 * pow26 * pow26);
    assert (as_nat5 to == as_nat5 tf + pow2 j * pow26 * pow26 * pow26 * pow26);
    lemma_mul_assos_5 (pow2 j) pow26 pow26 pow26 pow26;
    assert_norm (pow2 26 * pow2 26 * pow2 26 * pow26 = pow2 104);
    FStar.Math.Lemmas.pow2_plus j 104

val lset_bit5_lemma1:
    f:lseq uint64 5
  -> i:size_nat{i <= 128}
  -> Lemma
    (requires
      (forall (i:nat). i < 5 ==> v f.[i] <= max26) /\
      v f.[i / 26] + pow2 (i % 26) <= max26)
    (ensures (
      let fi = u64 (v f.[i / 26] + pow2 (i % 26)) in
      let out = f.[i / 26] <- fi in
      let f1 = (f.[0], f.[1], f.[2], f.[3], f.[4]) in
      let out1 = (out.[0], out.[1], out.[2], out.[3], out.[4]) in
      as_nat5 out1 % prime == pfadd (pow2 i) (as_nat5 f1 % prime)))
let lset_bit5_lemma1 f i =
  let fi = u64 (v f.[i / 26] + pow2 (i % 26)) in
  let out = f.[i / 26] <- fi in
  let f1 = (f.[0], f.[1], f.[2], f.[3], f.[4]) in
  let out1 = (out.[0], out.[1], out.[2], out.[3], out.[4]) in
  lset_bit5_lemma1_ f i;
  assert (as_nat5 out1 == pow2 i + as_nat5 f1);
  FStar.Math.Lemmas.lemma_mod_plus_distr_r
    (pow2 i) (as_nat5 f1) prime

val lemma_sum_lt_pow2_26: i:nat -> a:nat{a < pow2 (i % 26)} -> b:nat{b <= pow2 (i % 26)} ->
  Lemma (a + b <= max26)
let lemma_sum_lt_pow2_26 i a b =
  assert (a + b < pow2 (i % 26) + pow2 (i % 26));
  FStar.Math.Lemmas.pow2_le_compat 25 (i % 26);
  assert (a + b < pow2 25 + pow2 25);
  FStar.Math.Lemmas.pow2_double_sum 25;
  assert_norm (pow26 = pow2 26)

val lset_bit5:
    f:lseq uint64 5
  -> i:size_nat{i <= 128}
  -> Pure (lseq uint64 5)
    (requires
      (forall (i:nat). i < 5 ==> v f.[i] <= max26) /\
      as_nat5 (f.[0], f.[1], f.[2], f.[3], f.[4]) < pow2 i)
    (ensures fun out -> (
      let f1 = (f.[0], f.[1], f.[2], f.[3], f.[4]) in
      let out1 = (out.[0], out.[1], out.[2], out.[3], out.[4]) in
      (forall (i:nat). i < 5 ==> v out.[i] <= max26) /\
      as_nat5 out1 % prime == pfadd (pow2 i) (as_nat5 f1 % prime)))
let lset_bit5 f i =
  let b = u64 1 <<. size (i % 26) in
  let fi = f.[i / 26] in
  lset_bit5_lemma0 f i;
  assert (v fi < pow2 (i % 26));

  FStar.Math.Lemmas.pow2_lt_compat 26 (i % 26);
  FStar.Math.Lemmas.pow2_lt_compat 64 26;
  FStar.Math.Lemmas.modulo_lemma (pow2 (i % 26)) (pow2 64);
  assert (v b == pow2 (i % 26));
  logor_disjoint fi b (i % 26);
  let out_i = fi |. b in
  assert (v out_i == v fi + v b);
  assert (v out_i == v fi + pow2 (i % 26));
  lemma_sum_lt_pow2_26 i (v fi) (v b);
  assert_norm (pow26 = pow2 26);
  assert (v out_i <= max26);
  let out = f.[i / 26] <- out_i in
  lset_bit5_lemma1 f i;
  out

val set_bit5_lemma_k:
    #w:lanes
  -> f:lseq (uint64xN w) 5
  -> i:size_nat{i <= 128}
  -> k:nat{k < w}
  -> Lemma
    (requires
      lfelem_fits f (1, 1, 1, 1, 1) /\
      lfelem_less f (pow2 i))
    (ensures (
      let out = set_bit5 f i in
      tup64_fits5 (as_tup64_i (as_tup5 out) k) (1, 1, 1, 1, 1) /\
      (lfeval out).[k] == pfadd (pow2 i) (lfeval f).[k]))
let set_bit5_lemma_k #w f i k =
  let lf = create 5 (u64 0) in
  let lf = lf.[0] <- (vec_v f.[0]).[k] in
  let lf = lf.[1] <- (vec_v f.[1]).[k] in
  let lf = lf.[2] <- (vec_v f.[2]).[k] in
  let lf = lf.[3] <- (vec_v f.[3]).[k] in
  let lf = lf.[4] <- (vec_v f.[4]).[k] in
  let res = lset_bit5 lf i in

  let out = set_bit5 f i in
  let lout = create 5 (u64 0) in
  let lout = lout.[0] <- (vec_v out.[0]).[k] in
  let lout = lout.[1] <- (vec_v out.[1]).[k] in
  let lout = lout.[2] <- (vec_v out.[2]).[k] in
  let lout = lout.[3] <- (vec_v out.[3]).[k] in
  let lout = lout.[4] <- (vec_v out.[4]).[k] in
  eq_intro lout res

val add_mod_small: a:nat -> b:nat -> n:pos -> Lemma
  (requires a % n + b % n < n)
  (ensures  a % n + b % n == (a + b) % n)
let add_mod_small a b n =
  FStar.Math.Lemmas.modulo_lemma (a % n + b % n) n;
  assert (a % n + b % n == (a % n + b % n) % n);
  FStar.Math.Lemmas.lemma_mod_plus_distr_l a (b % n) n;
  FStar.Math.Lemmas.lemma_mod_plus_distr_r a b n

val mod_add128_sc:
    a:(uint64 & uint64)
  -> b:(uint64 & uint64)
  -> Pure (uint64 & uint64)
    (requires True)
    (ensures fun (r0, r1) ->
     let (a0, a1) = a in
     let (b0, b1) = b in
     v r1 * pow2 64 + v r0 ==
     ((v a1 + v b1) * pow2 64 + v a0 + v b0) % pow2 128)
let mod_add128_sc a b =
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
  let r2 = r1 +. c in
  assert (v c == (v a0 + v b0) / pow2 64);
  assert (v r2 == ((v a1 + v b1) % pow2 64 + (v a0 + v b0) / pow2 64) % pow2 64);
  assert (v r2 * pow2 64 == ((v a1 + v b1) % pow2 64 + (v a0 + v b0) / pow2 64) % pow2 64 * pow2 64);
  FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_2 ((v a1 + v b1) % pow2 64 + (v a0 + v b0) / pow2 64) 128 64;
  assert (v r2 * pow2 64 == ((v a1 + v b1) % pow2 64 + (v a0 + v b0) / pow2 64) * pow2 64 % pow2 128);
  assert (((v a1 + v b1) % pow2 64 + (v a0 + v b0) / pow2 64) * pow2 64 == (v a1 + v b1) % pow2 64 * pow2 64 + (v a0 + v b0) / pow2 64 * pow2 64);
  FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v a1 + v b1) 128 64;
  assert (v r2 * pow2 64 == ((v a1 + v b1) * pow2 64 % pow2 128 + (v a0 + v b0) / pow2 64 * pow2 64) % pow2 128);
  FStar.Math.Lemmas.lemma_mod_plus_distr_l ((v a1 + v b1) * pow2 64) ((v a0 + v b0) / pow2 64 * pow2 64) (pow2 128);
  assert (v r2 * pow2 64 == ((v a1 + v b1) * pow2 64 + (v a0 + v b0) / pow2 64 * pow2 64) % pow2 128);
  assert (v r0 == (v a0 + v b0) % pow2 64);
  FStar.Math.Lemmas.modulo_lemma ((v a0 + v b0) % pow2 64) (pow2 128);
  add_mod_small ((v a1 + v b1) * pow2 64 + (v a0 + v b0) / pow2 64 * pow2 64) ((v a0 + v b0) % pow2 64) (pow2 128);
  assert (v r2 * pow2 64 + v r0 == ((v a1 + v b1) * pow2 64 + (v a0 + v b0) / pow2 64 * pow2 64 + (v a0 + v b0) % pow2 64) % pow2 128);
  FStar.Math.Lemmas.euclidean_division_definition (v a0 + v b0) (pow2 64);
  assert (v r2 * pow2 64 + v r0 == ((v a1 + v b1) * pow2 64 + v a0 + v b0) % pow2 128);
  (r0, r2)

val mod_add128_lemma_i:
    #w:lanes
  -> a:(uint64xN w & uint64xN w)
  -> b:(uint64xN w & uint64xN w)
  -> i:nat{i < w}
  -> Lemma
    (let (r0, r1) = mod_add128_ws a b in
     let (a0, a1) = a in
     let (b0, b1) = b in
    (uint64xN_v r1).[i] * pow2 64 + (uint64xN_v r0).[i] ==
      (((uint64xN_v a1).[i] + (uint64xN_v b1).[i]) * pow2 64 +
      (uint64xN_v a0).[i] + (uint64xN_v b0).[i]) % pow2 128)
let mod_add128_lemma_i #w a b i =
  let (a0, a1) = a in
  let (b0, b1) = b in
  let (r0, r1) = mod_add128_ws a b in
  let (a0i, a1i) = ((vec_v a0).[i], (vec_v a1).[i]) in
  let (b0i, b1i) = ((vec_v b0).[i], (vec_v b1).[i]) in

  let r0s, r1s = mod_add128_sc (a0i, a1i) (b0i, b1i) in
  assert ((vec_v r0).[i] == r0s /\ (vec_v r1).[i] == r1s)
