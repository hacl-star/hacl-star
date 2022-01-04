module Hacl.Spec.K256.Field52.Lemmas

open FStar.Mul
open Lib.IntTypes

module S = Spec.K256

include Hacl.Spec.K256.Field52.Definitions
include Hacl.Spec.K256.Field52

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val load_felem5_lemma: s:felem4 ->
  Lemma (let f = load_felem5 s in
    felem_fits5 f (1,1,1,1,1) /\ as_nat5 f == as_nat4 s)


val store_felem5_lemma: f:felem5 -> Lemma
  (requires felem_fits5 f (1,1,1,1,1))
  (ensures  as_nat4 (store_felem5 f) == as_nat5 f)


val add5_lemma: m1:scale64_5 -> m2:scale64_5 -> f1:felem5 -> f2:felem5 -> Lemma
  (requires felem_fits5 f1 m1 /\ felem_fits5 f2 m2 /\ m1 +* m2 <=* (4096,4096,4096,4096,65536))
  (ensures (let r = add5 f1 f2 in
    as_nat5 r == as_nat5 f1 + as_nat5 f2 /\ felem_fits5 r (m1 +* m2)))


val fadd5_lemma: m1:scale64_5 -> m2:scale64_5 -> f1:felem5 -> f2:felem5 -> Lemma
  (requires felem_fits5 f1 m1 /\ felem_fits5 f2 m2 /\ m1 +* m2 <=* (4096,4096,4096,4096,65536))
  (ensures (let r = add5 f1 f2 in
    feval r == (feval f1 + feval f2) % S.prime /\ felem_fits5 r (m1 +* m2)))


val mul15_lemma: m1:scale64_5 -> m2:nat -> f:felem5 -> c:uint64 -> Lemma
  (requires felem_fits5 f m1 /\ v c <= m2 /\ m1 ** mk_nat5 m2 <=* (4096,4096,4096,4096,65536))
  (ensures (let r = mul15 f c in
    as_nat5 r == v c * as_nat5 f /\ felem_fits5 r (m1 ** mk_nat5 m2)))


val fmul15_lemma: m1:scale64_5 -> m2:nat -> f:felem5 -> c:uint64 -> Lemma
  (requires felem_fits5 f m1 /\ v c <= m2 /\ m1 ** mk_nat5 m2 <=* (4096,4096,4096,4096,65536))
  (ensures (let r = mul15 f c in
    feval r == v c * feval f % S.prime /\ felem_fits5 r (m1 ** mk_nat5 m2)))


val is_felem_zero_vartime5_lemma: f:felem5 ->
  Lemma (is_felem_zero_vartime5 f == (as_nat5 f = 0))


val is_felem_ge_prime_vartime5_lemma: f:felem5 -> Lemma
  (requires felem_fits5 f (1,1,1,1,1))
  (ensures  is_felem_ge_prime_vartime5 f == (as_nat5 f >= S.prime))


val is_felem_lt_vartime5_lemma: f1:felem5 -> f2:felem5 -> Lemma
  (requires felem_fits5 f1 (1,1,1,1,1) /\ felem_fits5 f2 (1,1,1,1,1))
  (ensures  is_felem_lt_vartime5 f1 f2 == (as_nat5 f1 < as_nat5 f2))


val is_felem_lt_prime_minus_order_vartime5_lemma: f:felem5 -> Lemma
  (requires felem_fits5 f (1,1,1,1,1))
  (ensures  is_felem_lt_prime_minus_order_vartime5 f == (as_nat5 f < S.prime - S.q))


val is_felem_eq_vartime5_lemma: f1:felem5 -> f2:felem5 -> Lemma
  (requires felem_fits5 f1 (1,1,1,1,1) /\ felem_fits5 f2 (1,1,1,1,1))
  (ensures  is_felem_eq_vartime5 f1 f2 == (as_nat5 f1 = as_nat5 f2))


val normalize_weak5_lemma: m:scale64_5 -> f:felem5 -> Lemma
  (requires (let (m0,m1,m2,m3,m4) = m in
    m0 + 1 <= 4096 /\ m1 + 1 <= 4096 /\
    m2 + 1 <= 4096 /\ m3 + 1 <= 4096 /\
    felem_fits5 f m))
  (ensures (let r = normalize_weak5 f in
    as_nat5 r % S.prime == as_nat5 f % S.prime
    /\ felem_fits5 r (1,1,1,1,2)))


val normalize5_lemma: m:scale64_5 -> f:felem5 -> Lemma
  (requires (let (m0,m1,m2,m3,m4) = m in
    m0 + 1 <= 4096 /\ m1 + 1 <= 4096 /\
    m2 + 1 <= 4096 /\ m3 + 1 <= 4096 /\
    felem_fits5 f m))
  (ensures (let r = normalize5 f in
    as_nat5 r == as_nat5 f % S.prime  /\
    felem_fits5 r (1,1,1,1,1)))
