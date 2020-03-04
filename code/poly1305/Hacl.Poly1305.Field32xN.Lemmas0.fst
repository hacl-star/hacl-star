module Hacl.Poly1305.Field32xN.Lemmas0

open Lib.IntTypes
open Lib.IntVector
open Lib.Sequence
open FStar.Mul
open FStar.Calc

open Hacl.Spec.Poly1305.Vec
include Hacl.Spec.Poly1305.Field32xN

#reset-options "--z3rlimit 50 --using_facts_from '* -FStar.Seq' --max_fuel 0 --max_ifuel 0"

val lemma_prime: unit -> Lemma (pow2 130 % prime = 5)
let lemma_prime () =
  assert_norm (pow2 130 % prime = 5 % prime);
  assert_norm (5 < prime);
  FStar.Math.Lemmas.modulo_lemma 5 prime

val lemma_mult_le: a:nat -> b:nat -> c:nat -> d:nat -> Lemma
  (requires a <= b /\ c <= d)
  (ensures  a * c <= b * d)
let lemma_mult_le a b c d = ()

val lemma_mul5_distr_l: a:nat -> b:nat -> c:nat -> d:nat -> e:nat -> f:nat -> Lemma
  (a * (b + c + d + e + f) == a * b + a * c + a * d + a * e + a * f)
let lemma_mul5_distr_l a b c d e f = ()

val lemma_mul5_distr_r: a:nat -> b:nat -> c:nat -> d:nat -> e:nat -> f:nat -> Lemma
  ((a + b + c + d + e) * f == a * f + b * f + c * f + d * f + e * f)
let lemma_mul5_distr_r a b c d e f = ()


val smul_mod_lemma:
    #m1:scale32
  -> #m2:scale32
  -> a:nat{a <= m1 * max26}
  -> b:nat{b <= m2 * max26} ->
  Lemma (a * b % pow2 64 == a * b)

let smul_mod_lemma #m1 #m2 a b =
  lemma_mult_le a (m1 * max26) b (m2 * max26);
  assert (a * b <= m1 * m2 * max26 * max26);
  FStar.Math.Lemmas.modulo_lemma (a * b) (pow2 64)


val smul_add_mod_lemma:
    #m1:scale32
  -> #m2:scale32
  -> #m3:scale64{m3 + m1 * m2 <= 4096}
  -> a:nat{a <= m1 * max26}
  -> b:nat{b <= m2 * max26}
  -> c:nat{c <= m3 * max26 * max26} ->
  Lemma ((c + a * b % pow2 64) % pow2 64 == c + a * b)

let smul_add_mod_lemma #m1 #m2 #m3 a b c =
  assert_norm ((m3 + m1 * m2) * max26 * max26 < pow2 64);
  lemma_mult_le a (m1 * max26) b (m2 * max26);
  assert (c + a * b <= m3 * max26 * max26 + m1 * m2 * max26 * max26);
  FStar.Math.Lemmas.modulo_lemma (c + a * b) (pow2 64)


#set-options "--initial_ifuel 1 --max_ifuel 1"

val fadd5_eval_lemma_i:
    #w:lanes
  -> f1:felem5 w{felem_fits5 f1 (2,2,2,2,2)}
  -> f2:felem5 w{felem_fits5 f2 (1,1,1,1,1)}
  -> i:nat{i < w} ->
  Lemma ((feval5 (fadd5 f1 f2)).[i] == pfadd (feval5 f1).[i] (feval5 f2).[i])

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


val smul_felem5_fits_lemma_i:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32
  -> u1:uint64xN w{felem_fits1 u1 m1}
  -> f2:uint64xN w{felem_fits1 f2 m2}
  -> i:nat{i < w} ->
  Lemma ((uint64xN_v (vec_mul_mod f2 u1)).[i] <= m1 * m2 * max26 * max26)

let smul_felem5_fits_lemma_i #w #m1 #m2 u1 f2 i =
  let o = vec_mul_mod f2 u1 in
  smul_mod_lemma #m1 #m2 (uint64xN_v u1).[i] (uint64xN_v f2).[i];
  assert ((uint64xN_v o).[i] == (uint64xN_v u1).[i] * (uint64xN_v f2).[i]);
  lemma_mult_le (uint64xN_v u1).[i] (m1 * max26) (uint64xN_v f2).[i] (m2 * max26)


val smul_felem5_eval_lemma_i:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32_5
  -> u1:uint64xN w{felem_fits1 u1 m1}
  -> f2:felem5 w{felem_fits5 f2 m2}
  -> i:nat{i < w} ->
  Lemma ((fas_nat5 (smul_felem5 #w u1 f2)).[i] == (uint64xN_v u1).[i] * (fas_nat5 f2).[i])

let smul_felem5_eval_lemma_i #w #m1 #m2 u1 f2 i =
  let o = smul_felem5 #w u1 f2 in
  let (m20, m21, m22, m23, m24) = m2 in
  let vu1 = (uint64xN_v u1).[i] in
  let (tf20, tf21, tf22, tf23, tf24) = as_tup64_i f2 i in
  let (to0, to1, to2, to3, to4) = as_tup64_i o i in

  smul_mod_lemma #m1 #m20 vu1 (v tf20);
  smul_mod_lemma #m1 #m21 vu1 (v tf21);
  smul_mod_lemma #m1 #m22 vu1 (v tf22);
  smul_mod_lemma #m1 #m23 vu1 (v tf23);
  smul_mod_lemma #m1 #m24 vu1 (v tf24);

  assert ((fas_nat5 o).[i] == vu1 * v tf20 + vu1 * v tf21 * pow26 + vu1 * v tf22 * pow52 +
    vu1 * v tf23 * pow78 + vu1 * v tf24 * pow104);

  calc (==) {
    vu1 * (fas_nat5 f2).[i];
  (==) { }
    vu1 * (v tf20 + v tf21 * pow26 + v tf22 * pow52 + v tf23 * pow78 + v tf24 * pow104);
  (==) { lemma_mul5_distr_l vu1 (v tf20) (v tf21 * pow26) (v tf22 * pow52) (v tf23 * pow78) (v tf24 * pow104)}
    vu1 * v tf20 + vu1 * (v tf21 * pow26) + vu1 * (v tf22 * pow52) + vu1 * (v tf23 * pow78) + vu1 * (v tf24 * pow104);
  (==) {
    FStar.Math.Lemmas.paren_mul_right vu1 (v tf21) pow26;
    FStar.Math.Lemmas.paren_mul_right vu1 (v tf22) pow52;
    FStar.Math.Lemmas.paren_mul_right vu1 (v tf23) pow78;
    FStar.Math.Lemmas.paren_mul_right vu1 (v tf24) pow104}
    vu1 * v tf20 + vu1 * v tf21 * pow26 + vu1 * v tf22 * pow52 + vu1 * v tf23 * pow78 + vu1 * v tf24 * pow104;
    };
  assert (vu1 * (fas_nat5 f2).[i] == (fas_nat5 o).[i])


val smul_felem5_fits_lemma1:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32
  -> u1:uint64xN w{felem_fits1 u1 m1}
  -> f2:uint64xN w{felem_fits1 f2 m2} ->
  Lemma (felem_wide_fits1 (vec_mul_mod f2 u1) (m1 * m2))

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
  -> u1:uint64xN w{felem_fits1 u1 m1}
  -> f2:felem5 w{felem_fits5 f2 m2} ->
  Lemma (felem_wide_fits5 (smul_felem5 #w u1 f2) (m1 *^ m2))

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
  -> u1:uint64xN w{felem_fits1 u1 m1}
  -> f2:felem5 w{felem_fits5 f2 m2} ->
  Lemma (fas_nat5 (smul_felem5 #w u1 f2) ==
    map2 #nat #nat #nat (fun a b -> a * b) (uint64xN_v u1) (fas_nat5 f2))

let smul_felem5_eval_lemma #w #m1 #m2 u1 f2 =
  FStar.Classical.forall_intro (smul_felem5_eval_lemma_i #w #m1 #m2 u1 f2);
  eq_intro (fas_nat5 (smul_felem5 #w u1 f2))
    (map2 #nat #nat #nat (fun a b -> a * b) (uint64xN_v u1) (fas_nat5 f2))


val smul_add_felem5_fits_lemma_i:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32
  -> #m3:scale64{m3 + m1 * m2 <= 4096}
  -> u1:uint64xN w{felem_fits1 u1 m1}
  -> f2:uint64xN w{felem_fits1 f2 m2}
  -> acc1:uint64xN w{felem_wide_fits1 acc1 m3}
  -> i:nat{i < w} ->
  Lemma ((uint64xN_v (vec_add_mod acc1 (vec_mul_mod f2 u1))).[i] <= (m3 + m1 * m2) * max26 * max26)

let smul_add_felem5_fits_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 i =
  let o = vec_add_mod acc1 (vec_mul_mod f2 u1) in
  smul_add_mod_lemma #m1 #m2 #m3 (uint64xN_v u1).[i] (uint64xN_v f2).[i] (uint64xN_v acc1).[i];
  assert ((uint64xN_v o).[i] == (uint64xN_v acc1).[i] + (uint64xN_v u1).[i] * (uint64xN_v f2).[i]);
  lemma_mult_le (uint64xN_v u1).[i] (m1 * max26) (uint64xN_v f2).[i] (m2 * max26);
  assert ((uint64xN_v o).[i] <= m3 * max26 * max26 + m1 * m2 * max26 * max26)


val smul_add_felem5_eval_lemma_i:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32_5
  -> #m3:scale64_5{m3 +* m1 *^ m2 <=* s64x5 4096}
  -> u1:uint64xN w{felem_fits1 u1 m1}
  -> f2:felem5 w{felem_fits5 f2 m2}
  -> acc1:felem_wide5 w{felem_wide_fits5 acc1 m3}
  -> i:nat{i < w} ->
  Lemma ((fas_nat5 (smul_add_felem5 #w u1 f2 acc1)).[i] ==
    (fas_nat5 acc1).[i] + (uint64xN_v u1).[i] * (fas_nat5 f2).[i])

let smul_add_felem5_eval_lemma_i #w #m1 #m2 #m3 u1 f2 acc1 i =
  let o = smul_add_felem5 #w u1 f2 acc1 in
  let (m20, m21, m22, m23, m24) = m2 in
  let (m30, m31, m32, m33, m34) = m3 in
  let vu1 = (uint64xN_v u1).[i] in
  let (tf20, tf21, tf22, tf23, tf24) = as_tup64_i f2 i in
  let (ta0, ta1, ta2, ta3, ta4) = as_tup64_i acc1 i in
  let (to0, to1, to2, to3, to4) = as_tup64_i o i in

  smul_add_mod_lemma #m1 #m20 #m30 vu1 (v tf20) (v ta0);
  smul_add_mod_lemma #m1 #m21 #m31 vu1 (v tf21) (v ta1);
  smul_add_mod_lemma #m1 #m22 #m32 vu1 (v tf22) (v ta2);
  smul_add_mod_lemma #m1 #m23 #m33 vu1 (v tf23) (v ta3);
  smul_add_mod_lemma #m1 #m24 #m34 vu1 (v tf24) (v ta4);

  calc (==) {
    (fas_nat5 o).[i];
    (==) { }
    v ta0 + vu1 * v tf20 + (v ta1 + vu1 * v tf21) * pow26 + (v ta2 + vu1 * v tf22) * pow52 +
    (v ta3 + vu1 * v tf23) * pow78 + (v ta4 + vu1 * v tf24) * pow104;
    (==) {
      FStar.Math.Lemmas.distributivity_add_left (v ta1) (vu1 * v tf21) pow26;
      FStar.Math.Lemmas.distributivity_add_left (v ta2) (vu1 * v tf22) pow52;
      FStar.Math.Lemmas.distributivity_add_left (v ta3) (vu1 * v tf23) pow78;
      FStar.Math.Lemmas.distributivity_add_left (v ta1) (vu1 * v tf24) pow104 }
    v ta0 + v ta1 * pow26 + v ta2 * pow52 + v ta3 * pow78 + v ta4 * pow104 +
    vu1 * v tf20 + vu1 * v tf21 * pow26 + vu1 * v tf22 * pow52 + vu1 * v tf23 * pow78 + vu1 * v tf24 * pow104;
    (==) { }
    (fas_nat5 acc1).[i] + vu1 * v tf20 + vu1 * v tf21 * pow26 + vu1 * v tf22 * pow52 + vu1 * v tf23 * pow78 + vu1 * v tf24 * pow104;
   };
   assert ((fas_nat5 o).[i] == (fas_nat5 acc1).[i] +
     vu1 * v tf20 + vu1 * v tf21 * pow26 + vu1 * v tf22 * pow52 + vu1 * v tf23 * pow78 + vu1 * v tf24 * pow104);

  calc (==) {
    vu1 * (fas_nat5 f2).[i];
  (==) { }
    vu1 * (v tf20 + v tf21 * pow26 + v tf22 * pow52 + v tf23 * pow78 + v tf24 * pow104);
  (==) { lemma_mul5_distr_l vu1 (v tf20) (v tf21 * pow26) (v tf22 * pow52) (v tf23 * pow78) (v tf24 * pow104)}
    vu1 * v tf20 + vu1 * (v tf21 * pow26) + vu1 * (v tf22 * pow52) + vu1 * (v tf23 * pow78) + vu1 * (v tf24 * pow104);
  (==) {
    FStar.Math.Lemmas.paren_mul_right vu1 (v tf21) pow26;
    FStar.Math.Lemmas.paren_mul_right vu1 (v tf22) pow52;
    FStar.Math.Lemmas.paren_mul_right vu1 (v tf23) pow78;
    FStar.Math.Lemmas.paren_mul_right vu1 (v tf24) pow104}
    vu1 * v tf20 + vu1 * v tf21 * pow26 + vu1 * v tf22 * pow52 + vu1 * v tf23 * pow78 + vu1 * v tf24 * pow104;
    };
  assert ((fas_nat5 o).[i] == (fas_nat5 acc1).[i] + vu1 * (fas_nat5 f2).[i])


val smul_add_felem5_fits_lemma1:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32
  -> #m3:scale64{m3 + m1 * m2 <= 4096}
  -> u1:uint64xN w{felem_fits1 u1 m1}
  -> f2:uint64xN w{felem_fits1 f2 m2}
  -> acc1:uint64xN w{felem_wide_fits1 acc1 m3} ->
  Lemma (felem_wide_fits1 (vec_add_mod acc1 (vec_mul_mod f2 u1)) (m3 + m1 * m2))

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
  -> #m3:scale64_5{m3 +* m1 *^ m2 <=* s64x5 4096}
  -> u1:uint64xN w{felem_fits1 u1 m1}
  -> f2:felem5 w{felem_fits5 f2 m2}
  -> acc1:felem_wide5 w{felem_wide_fits5 acc1 m3} ->
  Lemma (felem_wide_fits5 (smul_add_felem5 #w u1 f2 acc1) (m3 +* m1 *^ m2))

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
  -> #m3:scale64_5{m3 +* m1 *^ m2 <=* s64x5 4096}
  -> u1:uint64xN w{felem_fits1 u1 m1}
  -> f2:felem5 w{felem_fits5 f2 m2}
  -> acc1:felem_wide5 w{felem_wide_fits5 acc1 m3} ->
  Lemma (fas_nat5 (smul_add_felem5 #w u1 f2 acc1) ==
    map2 #nat #nat #nat (fun a b -> a + b) (fas_nat5 acc1)
      (map2 #nat #nat #nat (fun a b -> a * b) (uint64xN_v u1) (fas_nat5 f2)))

let smul_add_felem5_eval_lemma #w #m1 #m2 #m3 u1 f2 acc1 =
  let tmp =
    map2 #nat #nat #nat (fun a b -> a + b) (fas_nat5 acc1)
      (map2 #nat #nat #nat (fun a b -> a * b) (uint64xN_v u1) (fas_nat5 f2)) in
  FStar.Classical.forall_intro (smul_add_felem5_eval_lemma_i #w #m1 #m2 #m3 u1 f2 acc1);
  eq_intro (fas_nat5 (smul_add_felem5 #w u1 f2 acc1)) tmp


val lemma_fmul5_pow26: r:tup64_5 -> Lemma
  (requires (let (r0, r1, r2, r3, r4) = r in v r4 * 5 <= 10 * pow26))
  (ensures  (let (r0, r1, r2, r3, r4) = r in
    (pow26 * as_nat5 r) % prime == as_nat5 (r4 *! u64 5, r0, r1, r2, r3) % prime))

let lemma_fmul5_pow26 r =
  let (r0, r1, r2, r3, r4) = r in
  calc (==) {
    (pow26 * as_nat5 r) % prime;
  (==) { }
    (pow26 * (v r0 + v r1 * pow26 + v r2 * pow52 + v r3 * pow78 + v r4 * pow104)) % prime;
  (==) { lemma_mul5_distr_l pow26 (v r0) (v r1 * pow26) (v r2 * pow52) (v r3 * pow78) (v r4 * pow104) }
    (v r0 * pow26 + pow26 * v r1 * pow26 + pow26 * v r2 * pow52 + pow26 * v r3 * pow78 + pow26 * v r4 * pow104) % prime;
  (==) { }
    (v r0 * pow26 + v r1 * pow26 * pow26 + v r2 * pow26 * pow52 + v r3 * pow26 * pow78 + v r4 * pow26 * pow104) % prime;
  (==) {
    assert_norm (pow26 * pow26 = pow52);
    assert_norm (pow26 * pow52 = pow78);
    assert_norm (pow26 * pow78 = pow104);
    assert_norm (pow26 * pow104 = pow2 130) }
    (v r0 * pow26 + v r1 * pow52 + v r2 * pow78 + v r3 * pow104 + v r4 * pow2 130) % prime;
  (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_r
    (v r0 * pow26 + v r1 * pow52 + v r2 * pow78 + v r3 * pow104) (v r4 * pow2 130) prime }
    (v r0 * pow26 + v r1 * pow52 + v r2 * pow78 + v r3 * pow104 + (v r4 * pow2 130) % prime) % prime;
  (==) { FStar.Math.Lemmas.lemma_mod_mul_distr_r (v r4) (pow2 130) prime }
    (v r0 * pow26 + v r1 * pow52 + v r2 * pow78 + v r3 * pow104 + (v r4 * (pow2 130 % prime)) % prime) % prime;
  (==) { lemma_prime () }
    (v r0 * pow26 + v r1 * pow52 + v r2 * pow78 + v r3 * pow104 + (v r4 * 5) % prime) % prime;
  (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_r
    (v r0 * pow26 + v r1 * pow52 + v r2 * pow78 + v r3 * pow104) (v r4 * 5) prime }
    (v r0 * pow26 + v r1 * pow52 + v r2 * pow78 + v r3 * pow104 + v r4 * 5) % prime;
  };
  assert ((pow26 * as_nat5 r) % prime ==
    (v r0 * pow26 + v r1 * pow52 + v r2 * pow78 + v r3 * pow104 + v r4 * 5) % prime)


val lemma_fmul5_pow52: r:tup64_5 -> Lemma
  (requires (let (r0, r1, r2, r3, r4) = r in
    v r4 * 5 <= 10 * pow26 /\ v r3 * 5 <= 10 * pow26))
  (ensures (let (r0, r1, r2, r3, r4) = r in
    (pow52 * as_nat5 r) % prime == as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2) % prime))

let lemma_fmul5_pow52 r =
  let (r0, r1, r2, r3, r4) = r in
  calc (==) {
    (pow52 * as_nat5 r) % prime;
    (==) { assert_norm (pow52 == pow26 * pow26) }
    (pow26 * pow26 * as_nat5 r) % prime;
    (==) {
      FStar.Math.Lemmas.paren_mul_right pow26 pow26 (as_nat5 r);
      FStar.Math.Lemmas.lemma_mod_mul_distr_r pow26 (pow26 * as_nat5 r) prime }
    (pow26 * (pow26 * as_nat5 r % prime)) % prime;
    (==) { lemma_fmul5_pow26 r }
    (pow26 * (as_nat5 (r4 *! u64 5, r0, r1, r2, r3) % prime)) % prime;
    (==) { FStar.Math.Lemmas.lemma_mod_mul_distr_r pow26 (as_nat5 (r4 *! u64 5, r0, r1, r2, r3)) prime }
    (pow26 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3)) % prime;
    (==) { lemma_fmul5_pow26 (r4 *! u64 5, r0, r1, r2, r3) }
    as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2) % prime;
  };
  assert ((pow52 * as_nat5 r) % prime == as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2) % prime)


val lemma_fmul5_pow78: r:tup64_5 -> Lemma
  (requires (let (r0, r1, r2, r3, r4) = r in
    v r4 * 5 <= 10 * pow26 /\ v r3 * 5 <= 10 * pow26 /\ v r2 * 5 <= 10 * pow26))
  (ensures (let (r0, r1, r2, r3, r4) = r in
    (pow78 * as_nat5 r) % prime == as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1) % prime))

let lemma_fmul5_pow78 r =
  let (r0, r1, r2, r3, r4) = r in
  calc (==) {
    (pow78 * as_nat5 r) % prime;
    (==) { assert_norm (pow78 == pow26 * pow52) }
    (pow26 * pow52 * as_nat5 r) % prime;
    (==) {
      FStar.Math.Lemmas.paren_mul_right pow26 pow52 (as_nat5 r);
      FStar.Math.Lemmas.lemma_mod_mul_distr_r pow26 (pow52 * as_nat5 r) prime }
    (pow26 * (pow52 * as_nat5 r % prime)) % prime;
    (==) { lemma_fmul5_pow52 r }
    (pow26 * (as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2) % prime)) % prime;
    (==) { FStar.Math.Lemmas.lemma_mod_mul_distr_r pow26 (as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2)) prime }
    (pow26 * as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2)) % prime;
    (==) { lemma_fmul5_pow26 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2) }
    as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1) % prime;
  };
  assert ((pow78 * as_nat5 r) % prime == as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1) % prime)


val lemma_fmul5_pow104: r:tup64_5 -> Lemma
  (requires (let (r0, r1, r2, r3, r4) = r in
    v r4 * 5 <= 10 * pow26 /\ v r3 * 5 <= 10 * pow26 /\
    v r2 * 5 <= 10 * pow26 /\ v r1 * 5 <= 10 * pow26))
  (ensures (let (r0, r1, r2, r3, r4) = r in
    (pow104 * as_nat5 r) % prime == as_nat5 (r1 *! u64 5, r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0) % prime))

let lemma_fmul5_pow104 r =
  let (r0, r1, r2, r3, r4) = r in
  calc (==) {
    (pow104 * as_nat5 r) % prime;
    (==) { assert_norm (pow104 == pow26 * pow78) }
    (pow26 * pow78 * as_nat5 r) % prime;
    (==) {
      FStar.Math.Lemmas.paren_mul_right pow26 pow78 (as_nat5 r);
      FStar.Math.Lemmas.lemma_mod_mul_distr_r pow26 (pow78 * as_nat5 r) prime }
    (pow26 * (pow78 * as_nat5 r % prime)) % prime;
    (==) { lemma_fmul5_pow78 r }
    (pow26 * (as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1) % prime)) % prime;
    (==) { FStar.Math.Lemmas.lemma_mod_mul_distr_r pow26 (as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1)) prime }
    (pow26 * as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1)) % prime;
    (==) { lemma_fmul5_pow26 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1) }
    as_nat5 (r1 *! u64 5, r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0) % prime;
  };
  assert ((pow104 * as_nat5 r) % prime == as_nat5 (r1 *! u64 5, r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0) % prime)


val mul_felem5_lemma_1:
    f1:tup64_5{tup64_fits5 f1 (3, 3, 3, 3, 3)}
  -> r:tup64_5{tup64_fits5 r (2, 2, 2, 2, 2)} ->
  Lemma
  (let (f10, f11, f12, f13, f14) = f1 in
  let (r0, r1, r2, r3, r4) = r in
  (as_nat5 f1 * as_nat5 r) % prime ==
  (v f10 * as_nat5 r +
   v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3) +
   v f12 * pow52 * as_nat5 r + v f13 * pow78 * as_nat5 r + v f14 * pow104 * as_nat5 r) % prime)

let mul_felem5_lemma_1 f1 r =
  let (f10, f11, f12, f13, f14) = f1 in
  let (r0, r1, r2, r3, r4) = r in
  let tmp = v f10 * as_nat5 r + v f12 * pow52 * as_nat5 r + v f13 * pow78 * as_nat5 r + v f14 * pow104 * as_nat5 r in

  calc (==) {
    (as_nat5 f1 * as_nat5 r) % prime;
    (==) { }
    (v f10 + v f11 * pow26 + v f12 * pow52 + v f13 * pow78 + v f14 * pow104) * as_nat5 r % prime;
    (==) { lemma_mul5_distr_r (v f10) (v f11 * pow26) (v f12 * pow52) (v f13 * pow78) (v f14 * pow104) (as_nat5 r) }
    (v f10 * as_nat5 r + v f11 * pow26 * as_nat5 r + v f12 * pow52 * as_nat5 r + v f13 * pow78 * as_nat5 r + v f14 * pow104 * as_nat5 r) % prime;
    (==) {
      FStar.Math.Lemmas.lemma_mod_plus_distr_r tmp  (v f11 * pow26 * as_nat5 r) prime }
    (tmp + (v f11 * pow26 * as_nat5 r) % prime) % prime;
    (==) {
      FStar.Math.Lemmas.paren_mul_right (v f11) pow26 (as_nat5 r);
      FStar.Math.Lemmas.lemma_mod_mul_distr_r (v f11) (pow26 * as_nat5 r) prime }
    (tmp + v f11 * (pow26 * as_nat5 r % prime) % prime) % prime;
    (==) { lemma_fmul5_pow26 r }
    (tmp + v f11 * (as_nat5 (r4 *! u64 5, r0, r1, r2, r3) % prime) % prime) % prime;
    (==) { FStar.Math.Lemmas.lemma_mod_mul_distr_r (v f11) (as_nat5 (r4 *! u64 5, r0, r1, r2, r3)) prime }
    (tmp + v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3) % prime) % prime;
    (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_r tmp (v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3)) prime }
    (tmp + v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3)) % prime;
    };
  assert ((as_nat5 f1 * as_nat5 r) % prime == (tmp + v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3)) % prime)


val mul_felem5_lemma_2:
    f1:tup64_5{tup64_fits5 f1 (3, 3, 3, 3, 3)}
  -> r:tup64_5{tup64_fits5 r (2, 2, 2, 2, 2)} ->
  Lemma
  (let (f10, f11, f12, f13, f14) = f1 in
  let (r0, r1, r2, r3, r4) = r in
  (as_nat5 f1 * as_nat5 r) % prime ==
  (v f10 * as_nat5 r +
   v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3) +
   v f12 * as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2) +
   v f13 * pow78 * as_nat5 r + v f14 * pow104 * as_nat5 r) % prime)

let mul_felem5_lemma_2 f1 r =
  let (f10, f11, f12, f13, f14) = f1 in
  let (r0, r1, r2, r3, r4) = r in
  let tmp =
    v f10 * as_nat5 r + v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3) +
    v f13 * pow78 * as_nat5 r + v f14 * pow104 * as_nat5 r in

  calc (==) {
    (as_nat5 f1 * as_nat5 r) % prime;
    (==) { mul_felem5_lemma_1 f1 r }
    (tmp + v f12 * pow52 * as_nat5 r) % prime;
    (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_r tmp (v f12 * pow52 * as_nat5 r) prime }
    (tmp + (v f12 * pow52 * as_nat5 r) % prime) % prime;
    (==) {
      FStar.Math.Lemmas.paren_mul_right (v f12) pow52 (as_nat5 r);
      FStar.Math.Lemmas.lemma_mod_mul_distr_r (v f12) (pow52 * as_nat5 r) prime }
    (tmp + v f12 * (pow52 * as_nat5 r % prime) % prime) % prime;
    (==) { lemma_fmul5_pow52 r }
    (tmp + v f12 * (as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2) % prime) % prime) % prime;
    (==) { FStar.Math.Lemmas.lemma_mod_mul_distr_r (v f12) (as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2)) prime }
    (tmp + v f12 * as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2) % prime) % prime;
    (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_r tmp (v f12 * as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2)) prime }
    (tmp + v f12 * as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2)) % prime;
   };
  assert ((as_nat5 f1 * as_nat5 r) % prime == (tmp + v f12 * as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2)) % prime)


val mul_felem5_lemma_3:
    f1:tup64_5{tup64_fits5 f1 (3, 3, 3, 3, 3)}
  -> r:tup64_5{tup64_fits5 r (2, 2, 2, 2, 2)} ->
  Lemma
  (let (f10, f11, f12, f13, f14) = f1 in
  let (r0, r1, r2, r3, r4) = r in
  (as_nat5 f1 * as_nat5 r) % prime ==
  (v f10 * as_nat5 r +
   v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3) +
   v f12 * as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2) +
   v f13 * as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1) +
   v f14 * pow104 * as_nat5 r) % prime)

let mul_felem5_lemma_3 f1 r =
  let (f10, f11, f12, f13, f14) = f1 in
  let (r0, r1, r2, r3, r4) = r in
  let tmp =
    v f10 * as_nat5 r + v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3) +
    v f12 * as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2) + v f14 * pow104 * as_nat5 r in

  calc (==) {
    (as_nat5 f1 * as_nat5 r) % prime;
    (==) { mul_felem5_lemma_2 f1 r }
    (tmp +  v f13 * pow78 * as_nat5 r) % prime;
    (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_r tmp (v f13 * pow78 * as_nat5 r) prime }
    (tmp + (v f13 * pow78 * as_nat5 r) % prime) % prime;
    (==) {
      FStar.Math.Lemmas.paren_mul_right (v f13) pow78 (as_nat5 r);
      FStar.Math.Lemmas.lemma_mod_mul_distr_r (v f13) (pow78 * as_nat5 r) prime }
    (tmp + v f13 * (pow78 * as_nat5 r % prime) % prime) % prime;
    (==) { lemma_fmul5_pow78 r }
    (tmp + v f13 * (as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1) % prime) % prime) % prime;
    (==) { FStar.Math.Lemmas.lemma_mod_mul_distr_r (v f13) (as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1)) prime }
    (tmp + v f13 * as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1) % prime) % prime;
    (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_r tmp (v f13 * as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1)) prime }
    (tmp + v f13 * as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1)) % prime;
   };
  assert ((as_nat5 f1 * as_nat5 r) % prime == (tmp + v f13 * as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1)) % prime)


val mul_felem5_lemma_4:
    f1:tup64_5{tup64_fits5 f1 (3, 3, 3, 3, 3)}
  -> r:tup64_5{tup64_fits5 r (2, 2, 2, 2, 2)} ->
  Lemma
  (let (f10, f11, f12, f13, f14) = f1 in
  let (r0, r1, r2, r3, r4) = r in
  (as_nat5 f1 * as_nat5 r) % prime ==
  (v f10 * as_nat5 r +
   v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3) +
   v f12 * as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2) +
   v f13 * as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1) +
   v f14 * as_nat5 (r1 *! u64 5, r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0)) % prime)

let mul_felem5_lemma_4 f1 r =
  let (f10, f11, f12, f13, f14) = f1 in
  let (r0, r1, r2, r3, r4) = r in
  let tmp =
    v f10 * as_nat5 r + v f11 * as_nat5 (r4 *! u64 5, r0, r1, r2, r3) +
    v f12 * as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2) + v f13 * as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1) in

  calc (==) {
    (as_nat5 f1 * as_nat5 r) % prime;
    (==) { mul_felem5_lemma_3 f1 r }
    (tmp + v f14 * pow104 * as_nat5 r) % prime;
    (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_r tmp (v f14 * pow104 * as_nat5 r) prime }
    (tmp + (v f14 * pow104 * as_nat5 r) % prime) % prime;
    (==) {
      FStar.Math.Lemmas.paren_mul_right (v f14) pow104 (as_nat5 r);
      FStar.Math.Lemmas.lemma_mod_mul_distr_r (v f14) (pow104 * as_nat5 r) prime }
    (tmp + v f14 * (pow104 * as_nat5 r % prime) % prime) % prime;
    (==) { lemma_fmul5_pow104 r }
    (tmp + v f14 * (as_nat5 (r1 *! u64 5, r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0) % prime) % prime) % prime;
    (==) { FStar.Math.Lemmas.lemma_mod_mul_distr_r (v f14) (as_nat5 (r1 *! u64 5, r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0)) prime }
    (tmp + v f14 * as_nat5 (r1 *! u64 5, r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0) % prime) % prime;
    (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_r tmp (v f14 * as_nat5 (r1 *! u64 5, r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0)) prime }
    (tmp + v f14 * as_nat5 (r1 *! u64 5, r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0)) % prime;
   };
  assert ((as_nat5 f1 * as_nat5 r) % prime == (tmp + v f14 * as_nat5 (r1 *! u64 5, r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0)) % prime)


val mul_felem5_lemma:
    f1:tup64_5{tup64_fits5 f1 (3, 3, 3, 3, 3)}
  -> r:tup64_5{tup64_fits5 r (2, 2, 2, 2, 2)} ->
  Lemma
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
  mul_felem5_lemma_4 f1 r;
  FStar.Math.Lemmas.lemma_mod_mul_distr_l (as_nat5 f1) (as_nat5 r) prime;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (as_nat5 f1 % prime) (as_nat5 r) prime


val precomp_r5_as_tup64:
    #w:lanes
  -> r:felem5 w{felem_fits5 r (2, 2, 2, 2, 2)}
  -> i:nat{i < w} ->
  Lemma
  (let r5 = precomp_r5 r in
   let (tr50, tr51, tr52, tr53, tr54) = as_tup64_i r5 i in
   let (tr0, tr1, tr2, tr3, tr4) = as_tup64_i r i in
   tr50 == tr0 *! u64 5 /\
   tr51 == tr1 *! u64 5 /\
   tr52 == tr2 *! u64 5 /\
   tr53 == tr3 *! u64 5 /\
   tr54 == tr4 *! u64 5)

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
  assert (v tr50 == v (tr0 *! u64 5));
  assert (v tr51 == v (tr1 *! u64 5));
  assert (v tr52 == v (tr2 *! u64 5));
  assert (v tr53 == v (tr3 *! u64 5));
  assert (v tr54 == v (tr4 *! u64 5))


val mul_felem5_eval_as_tup64:
    #w:lanes
  -> f1:felem5 w{felem_fits5 f1 (3, 3, 3, 3, 3)}
  -> r:felem5 w{felem_fits5 r (2, 2, 2, 2, 2)}
  -> r5:felem5 w{felem_fits5 r5 (10, 10, 10, 10, 10) /\ r5 == precomp_r5 r}
  -> i:nat{i < w} ->
  Lemma
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
   v tf14 * as_nat5 (tr1 *! u64 5, tr2 *! u64 5, tr3 *! u64 5, tr4 *! u64 5, tr0)))

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
