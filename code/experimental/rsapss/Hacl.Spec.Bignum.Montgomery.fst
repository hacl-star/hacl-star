module Hacl.Spec.Bignum.Montgomery

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.LoopCombinators

open Hacl.Spec.Bignum
open Hacl.Spec.Bignum.Base
open Hacl.Spec.Bignum.Addition
open Hacl.Spec.Bignum.Multiplication


module M = Hacl.Spec.Bignum.Montgomery.Lemmas
module BL = Hacl.Spec.Bignum.Lemmas

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val mont_reduction_:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> j:size_nat{j < rLen}
  -> res:lbignum (rLen + rLen) ->
  lbignum (rLen + rLen)

let mont_reduction_ #nLen #rLen n nInv_u64 j res =
  let qj = nInv_u64 *. res.[j] in
  let res' = sub res j nLen in
  let c, res' = bn_mul_by_limb_add #nLen n qj res' in
  let res = update_sub res j nLen res' in

  let res' = sub res (j + nLen) (rLen + rLen - j - nLen) in
  let _, res' = bn_add res' (create 1 c) in
  update_sub res (j + nLen) (rLen + rLen - j - nLen) res'


val mont_reduction:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> c:lbignum (rLen + rLen) ->
  lbignum rLen

let mont_reduction #nLen #rLen n nInv_u64 c =
  let c = repeati rLen (mont_reduction_ #nLen #rLen n nInv_u64) c in
  sub c rLen rLen


val to_mont:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> r2:lbignum nLen
  -> a:lbignum nLen ->
  aM:lbignum rLen

let to_mont #nLen #rLen n nInv_u64 r2 a =
  let c = bn_mul a r2 in // c = a * r2
  let tmp = create (rLen + rLen) (u64 0) in
  let tmp = update_sub tmp 0 (nLen + nLen) c in
  mont_reduction #nLen #rLen n nInv_u64 tmp // aM = c % n


val from_mont:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> aM:lbignum rLen ->
  a:lbignum nLen

let from_mont #nLen #rLen n nInv_u64 aM =
  let tmp = create (rLen + rLen) (u64 0) in
  let tmp = update_sub tmp 0 rLen aM in
  let a' = mont_reduction #nLen #rLen n nInv_u64 tmp in
  sub a' 0 nLen


val mul_mod_mont:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> aM:lbignum rLen
  -> bM:lbignum rLen ->
  resM:lbignum rLen

let mul_mod_mont #nLen #rLen n nInv_u64 aM bM =
  let c = bn_mul aM bM in // c = aM * bM
  mont_reduction n nInv_u64 c // resM = c % n


val mont_reduction_lemma:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> c:lbignum (rLen + rLen) -> Lemma
  (requires
    (1 + (bn_v n % pow2 64) * v mu) % pow2 64 == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    bn_v c < 4 * bn_v n * bn_v n)
  (ensures
    (let res = bn_v (mont_reduction #nLen #rLen n mu c) in
    res == M.mont_reduction rLen (bn_v n) (v mu) (bn_v c) /\
    res < 2 * bn_v n))

let mont_reduction_lemma #nLen #rLen n mu c =
  assume (bn_v (mont_reduction #nLen #rLen n mu c) == M.mont_reduction rLen (bn_v n) (v mu) (bn_v c));
  let d, k = BL.eea_pow2_odd (64 * rLen) (bn_v n) in
  BL.mod_exp_mont_preconditions rLen (bn_v n) (v mu);
  BL.mod_exp_mont_preconditions_rLen nLen (bn_v n);
  M.mont_mult_lemma_fits rLen (bn_v n) d (v mu) (bn_v c)


val to_mont_lemma:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> r2:lbignum nLen
  -> a:lbignum nLen -> Lemma
  (requires
    (1 + (bn_v n % pow2 64) * v mu) % pow2 64 == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    bn_v a < bn_v n /\ bn_v r2 == pow2 (128 * rLen) % bn_v n)
  (ensures
   (let aM = bn_v (to_mont #nLen #rLen n mu r2 a) in
    aM == M.to_mont rLen (bn_v n) (v mu) (bn_v a) /\
    aM < 2 * bn_v n))

let to_mont_lemma #nLen #rLen n mu r2 a =
  assume (bn_v (to_mont #nLen #rLen n mu r2 a) == M.to_mont rLen (bn_v n) (v mu) (bn_v a));
  let d, k = BL.eea_pow2_odd (64 * rLen) (bn_v n) in
  BL.mod_exp_mont_preconditions rLen (bn_v n) (v mu);
  BL.mod_exp_mont_preconditions_rLen nLen (bn_v n);
  M.to_mont_lemma_fits rLen (bn_v n) d (v mu) (bn_v a)


val from_mont_lemma:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> aM:lbignum rLen -> Lemma
  (requires
    (1 + (bn_v n % pow2 64) * v mu) % pow2 64 == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    bn_v aM < 2 * bn_v n)
  (ensures
   (let a = bn_v (from_mont #nLen #rLen n mu aM) in
    a == M.from_mont rLen (bn_v n) (v mu) (bn_v aM) /\
    a <= bn_v n))

let from_mont_lemma #nLen #rLen n mu aM =
  assume (bn_v (from_mont #nLen #rLen n mu aM) == M.from_mont rLen (bn_v n) (v mu) (bn_v aM));
  let d, k = BL.eea_pow2_odd (64 * rLen) (bn_v n) in
  BL.mod_exp_mont_preconditions rLen (bn_v n) (v mu);
  BL.mod_exp_mont_preconditions_rLen nLen (bn_v n);
  M.from_mont_lemma_fits rLen (bn_v n) d (v mu) (bn_v aM)


val mul_mod_mont_lemma:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> aM:lbignum rLen
  -> bM:lbignum rLen -> Lemma
  (requires
    (1 + (bn_v n % pow2 64) * v mu) % pow2 64 == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    bn_v aM < 2 * bn_v n /\ bn_v bM < 2 * bn_v n)
  (ensures
    (let res = bn_v (mul_mod_mont #nLen #rLen n mu aM bM) in
    res == M.mont_mul rLen (bn_v n) (v mu) (bn_v aM) (bn_v bM) /\
    res < 2 * bn_v n))

let mul_mod_mont_lemma #nLen #rLen n mu aM bM =
  assume (bn_v (mul_mod_mont #nLen #rLen n mu aM bM) == M.mont_mul rLen (bn_v n) (v mu) (bn_v aM) (bn_v bM));
  let d, k = BL.eea_pow2_odd (64 * rLen) (bn_v n) in
  BL.mod_exp_mont_preconditions rLen (bn_v n) (v mu);
  BL.mod_exp_mont_preconditions_rLen nLen (bn_v n);
  M.mont_mul_lemma_fits rLen (bn_v n) d (v mu) (bn_v aM) (bn_v bM)
