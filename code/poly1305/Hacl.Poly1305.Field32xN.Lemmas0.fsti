module Hacl.Poly1305.Field32xN.Lemmas0

open Lib.IntTypes
open Lib.IntVector
open Lib.Sequence
open FStar.Mul

open Hacl.Spec.Poly1305.Vec
include Hacl.Spec.Poly1305.Field32xN

val smul_mod_lemma:
    #m1:scale32
  -> #m2:scale32
  -> a:nat{a <= m1 * max26}
  -> b:nat{b <= m2 * max26} ->
  Lemma (a * b % pow2 64 == a * b)

val smul_add_mod_lemma:
    #m1:scale32
  -> #m2:scale32
  -> #m3:scale64{m3 + m1 * m2 <= 4096}
  -> a:nat{a <= m1 * max26}
  -> b:nat{b <= m2 * max26}
  -> c:nat{c <= m3 * max26 * max26} ->
  Lemma ((c + a * b % pow2 64) % pow2 64 == c + a * b)

val add5_lemma1: ma:scale64 -> mb:scale64 -> a:uint64 -> b:uint64 -> Lemma
  (requires v a <= ma * max26 /\ v b <= mb * max26 /\ ma + mb <= 64)
  (ensures  v (a +. b) == v a + v b /\ v (a +. b) <= (ma + mb) * max26)

val fadd5_eval_lemma_i:
    #w:lanes
  -> f1:felem5 w{felem_fits5 f1 (2,2,2,2,2)}
  -> f2:felem5 w{felem_fits5 f2 (1,1,1,1,1)}
  -> i:nat{i < w} ->
  Lemma ((feval5 (fadd5 f1 f2)).[i] == pfadd (feval5 f1).[i] (feval5 f2).[i])

val smul_felem5_fits_lemma_i:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32
  -> u1:uint64xN w{felem_fits1 u1 m1}
  -> f2:uint64xN w{felem_fits1 f2 m2}
  -> i:nat{i < w} ->
  Lemma ((uint64xN_v (vec_mul_mod f2 u1)).[i] <= m1 * m2 * max26 * max26)

val smul_felem5_eval_lemma_i:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32_5
  -> u1:uint64xN w{felem_fits1 u1 m1}
  -> f2:felem5 w{felem_fits5 f2 m2}
  -> i:nat{i < w} ->
  Lemma ((fas_nat5 (smul_felem5 #w u1 f2)).[i] == (uint64xN_v u1).[i] * (fas_nat5 f2).[i])

val smul_felem5_fits_lemma1:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32
  -> u1:uint64xN w{felem_fits1 u1 m1}
  -> f2:uint64xN w{felem_fits1 f2 m2} ->
  Lemma (felem_wide_fits1 (vec_mul_mod f2 u1) (m1 * m2))

val smul_felem5_fits_lemma:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32_5
  -> u1:uint64xN w{felem_fits1 u1 m1}
  -> f2:felem5 w{felem_fits5 f2 m2} ->
  Lemma (felem_wide_fits5 (smul_felem5 #w u1 f2) (m1 *^ m2))

val smul_felem5_eval_lemma:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32_5
  -> u1:uint64xN w{felem_fits1 u1 m1}
  -> f2:felem5 w{felem_fits5 f2 m2} ->
  Lemma (fas_nat5 (smul_felem5 #w u1 f2) ==
    map2 #nat #nat #nat (fun a b -> a * b) (uint64xN_v u1) (fas_nat5 f2))

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

val smul_add_felem5_fits_lemma1:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32
  -> #m3:scale64{m3 + m1 * m2 <= 4096}
  -> u1:uint64xN w{felem_fits1 u1 m1}
  -> f2:uint64xN w{felem_fits1 f2 m2}
  -> acc1:uint64xN w{felem_wide_fits1 acc1 m3} ->
  Lemma (felem_wide_fits1 (vec_add_mod acc1 (vec_mul_mod f2 u1)) (m3 + m1 * m2))

val smul_add_felem5_fits_lemma:
    #w:lanes
  -> #m1:scale32
  -> #m2:scale32_5
  -> #m3:scale64_5{m3 +* m1 *^ m2 <=* s64x5 4096}
  -> u1:uint64xN w{felem_fits1 u1 m1}
  -> f2:felem5 w{felem_fits5 f2 m2}
  -> acc1:felem_wide5 w{felem_wide_fits5 acc1 m3} ->
  Lemma (felem_wide_fits5 (smul_add_felem5 #w u1 f2 acc1) (m3 +* m1 *^ m2))

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

val lemma_fmul5_pow26: r:tup64_5 -> Lemma
  (requires (let (r0, r1, r2, r3, r4) = r in v r4 * 5 <= 10 * pow26))
  (ensures  (let (r0, r1, r2, r3, r4) = r in
    (pow26 * as_nat5 r) % prime == as_nat5 (r4 *! u64 5, r0, r1, r2, r3) % prime))

val lemma_fmul5_pow52: r:tup64_5 -> Lemma
  (requires (let (r0, r1, r2, r3, r4) = r in
    v r4 * 5 <= 10 * pow26 /\ v r3 * 5 <= 10 * pow26))
  (ensures (let (r0, r1, r2, r3, r4) = r in
    (pow52 * as_nat5 r) % prime == as_nat5 (r3 *! u64 5, r4 *! u64 5, r0, r1, r2) % prime))

val lemma_fmul5_pow78: r:tup64_5 -> Lemma
  (requires (let (r0, r1, r2, r3, r4) = r in
    v r4 * 5 <= 10 * pow26 /\ v r3 * 5 <= 10 * pow26 /\ v r2 * 5 <= 10 * pow26))
  (ensures (let (r0, r1, r2, r3, r4) = r in
    (pow78 * as_nat5 r) % prime == as_nat5 (r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0, r1) % prime))

val lemma_fmul5_pow104: r:tup64_5 -> Lemma
  (requires (let (r0, r1, r2, r3, r4) = r in
    v r4 * 5 <= 10 * pow26 /\ v r3 * 5 <= 10 * pow26 /\
    v r2 * 5 <= 10 * pow26 /\ v r1 * 5 <= 10 * pow26))
  (ensures (let (r0, r1, r2, r3, r4) = r in
    (pow104 * as_nat5 r) % prime == as_nat5 (r1 *! u64 5, r2 *! u64 5, r3 *! u64 5, r4 *! u64 5, r0) % prime))

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
