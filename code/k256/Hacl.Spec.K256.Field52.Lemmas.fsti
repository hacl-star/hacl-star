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
    feval5 r == (feval5 f1 + feval5 f2) % S.prime /\ felem_fits5 r (m1 +* m2)))


val mul15_lemma: m1:scale64_5 -> m2:nat -> f:felem5 -> c:uint64 -> Lemma
  (requires felem_fits5 f m1 /\ v c <= m2 /\ m1 ** mk_nat5 m2 <=* (4096,4096,4096,4096,65536))
  (ensures (let r = mul15 f c in
    as_nat5 r == v c * as_nat5 f /\ felem_fits5 r (m1 ** mk_nat5 m2)))


val fmul15_lemma: m1:scale64_5 -> m2:nat -> f:felem5 -> c:uint64 -> Lemma
  (requires felem_fits5 f m1 /\ v c <= m2 /\ m1 ** mk_nat5 m2 <=* (4096,4096,4096,4096,65536))
  (ensures (let r = mul15 f c in
    feval5 r == v c * feval5 f % S.prime /\ felem_fits5 r (m1 ** mk_nat5 m2)))


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


val fmul5_lemma: a:felem5 -> b:felem5 -> Lemma
  (requires
    felem_fits5 a (8,8,8,8,8) /\
    felem_fits5 b (8,8,8,8,8))
  (ensures (let res = fmul5 a b in
    as_nat5 res % S.prime == as_nat5 a * as_nat5 b % S.prime  /\
    felem_fits5 res (1,1,1,1,2)))


val fmul5_lemma1: a:felem5 -> b:felem5 -> Lemma
  (requires
    felem_fits5 a (8,8,8,8,8) /\
    felem_fits5 b (8,8,8,8,8))
  (ensures (let res = fmul5 a b in
    feval5 res == feval5 a * feval5 b % S.prime  /\
    felem_fits5 res (1,1,1,1,2)))


val fsqr5_lemma: a:felem5 -> Lemma
  (requires
    felem_fits5 a (8,8,8,8,8))
  (ensures (let res = fsqr5 a in
    as_nat5 res % S.prime == as_nat5 a * as_nat5 a % S.prime  /\
    felem_fits5 res (1,1,1,1,2)))


val fsqr5_lemma1: a:felem5 -> Lemma
  (requires
    felem_fits5 a (8,8,8,8,8))
  (ensures (let res = fsqr5 a in
    feval5 res == feval5 a * feval5 a % S.prime  /\
    felem_fits5 res (1,1,1,1,2)))


val sub5_lemma (ma mb:scale64_5) (a b:felem5) (x:uint64) : Lemma
  (requires (let xn = v x in
    let (ma0,ma1,ma2,ma3,ma4) = ma in
    let (mb0,mb1,mb2,mb3,mb4) = mb in 2 * xn <= 4096 /\
    mb0 <= xn /\ mb1 <= xn /\ mb2 <= xn /\ mb3 <= xn /\ mb4 <= xn /\
    ma0+2*xn <= 4096 /\ ma1+2*xn <= 4096 /\
    ma2+2*xn <= 4096 /\ ma3+2*xn <= 4096 /\
    ma4+2*xn <= 65536 /\
    felem_fits5 a ma /\ felem_fits5 b mb))
  (ensures (let r = fsub5 a b x in let xn = v x in
    let (ma0,ma1,ma2,ma3,ma4) = ma in
    as_nat5 r = as_nat5 a + 2 * xn * S.prime - as_nat5 b /\
    felem_fits5 r (ma0+2*xn,ma1+2*xn,ma2+2*xn,ma3+2*xn,ma4+2*xn)))


val fsub5_lemma (ma mb:scale64_5) (a b:felem5) (x:uint64) : Lemma
  (requires (let xn = v x in
    let (ma0,ma1,ma2,ma3,ma4) = ma in
    let (mb0,mb1,mb2,mb3,mb4) = mb in 2 * xn <= 4096 /\
    mb0 <= xn /\ mb1 <= xn /\ mb2 <= xn /\ mb3 <= xn /\ mb4 <= xn /\
    ma0+2*xn <= 4096 /\ ma1+2*xn <= 4096 /\
    ma2+2*xn <= 4096 /\ ma3+2*xn <= 4096 /\
    ma4+2*xn <= 65536 /\
    felem_fits5 a ma /\ felem_fits5 b mb))
  (ensures (let r = fsub5 a b x in let xn = v x in
    let (ma0,ma1,ma2,ma3,ma4) = ma in
    feval5 r = (feval5 a - feval5 b) % S.prime /\
    felem_fits5 r (ma0+2*xn,ma1+2*xn,ma2+2*xn,ma3+2*xn,ma4+2*xn)))
