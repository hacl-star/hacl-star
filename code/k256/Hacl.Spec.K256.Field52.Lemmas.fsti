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
    as_nat5 r == as_nat5 f * v c /\ felem_fits5 r (m1 ** mk_nat5 m2)))


val fmul15_lemma: m1:scale64_5 -> m2:nat -> f:felem5 -> c:uint64 -> Lemma
  (requires felem_fits5 f m1 /\ v c <= m2 /\ m1 ** mk_nat5 m2 <=* (4096,4096,4096,4096,65536))
  (ensures (let r = mul15 f c in
    feval r == feval f * v c % S.prime /\ felem_fits5 r (m1 ** mk_nat5 m2)))


val lemma_as_nat_bound: f:felem5 -> Lemma
  (requires felem_fits5 f (1,1,1,1,1))
  (ensures as_nat5 f < pow2 256)


val lemma_as_nat_decompose: f:felem5 -> Lemma
  (requires felem_fits5 f (1,1,1,1,1))
  (ensures (let (f0,f1,f2,f3,f4) = f in
    v f4 = as_nat5 f / pow208 /\
    v f3 = as_nat5 f % pow208 / pow156 /\
    v f2 = as_nat5 f % pow156 / pow104 /\
    v f1 = as_nat5 f % pow104 / pow52 /\
    v f0 = as_nat5 f % pow52))


val as_nat_inj (f1 f2: felem5) : Lemma
  (requires
    felem_fits5 f1 (1,1,1,1,1) /\ felem_fits5 f2 (1,1,1,1,1) /\
    as_nat5 f1 == as_nat5 f2)
  (ensures
   (let (a0,a1,a2,a3,a4) = f1 in let (b0,b1,b2,b3,b4) = f2 in
    a0 == b0 /\ a1 == b1 /\ a2 == b2 /\ a3 == b3 /\ a4 == b4))


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
    as_nat5 r % S.prime == as_nat5 f % S.prime /\ felem_fits5 r (1,1,1,1,2)))
