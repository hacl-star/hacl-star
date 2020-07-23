module Hacl.Spec.Bignum.Exponentiation

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.LoopCombinators

open Hacl.Spec.Bignum.Definitions
open Hacl.Spec.Bignum
open Hacl.Spec.Bignum.Montgomery
open Hacl.Spec.Bignum.ModInv64

module BL = Hacl.Spec.Exponentiation.Lemmas
module M = Hacl.Spec.Montgomery.Lemmas

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val bn_mod_exp_f:
    #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> bBits:size_pos
  -> bLen:size_nat{bLen == blocks bBits 64}
  -> b:lbignum bLen
  -> i:nat{i < bBits}
  -> aM_accM: tuple2 (lbignum nLen) (lbignum nLen) ->
  tuple2 (lbignum nLen) (lbignum nLen)

let bn_mod_exp_f #nLen n mu bBits bLen b i (aM, accM) =
  let accM = if (bn_is_bit_set #bLen b i) then mont_mul n mu aM accM else accM in // acc = (acc * a) % n
  let aM = mont_sqr n mu aM in // a = (a * a) % n
  (aM, accM)


val bn_mod_exp_mont:
    modBits:size_pos
  -> nLen:size_pos{128 * nLen <= max_size_t}
  -> n:lbignum nLen{nLen == blocks modBits 64}
  -> a:lbignum nLen
  -> acc:lbignum nLen
  -> bBits:size_pos
  -> b:lbignum (blocks bBits 64) ->
  lbignum nLen

let bn_mod_exp_mont modBits nLen n a acc bBits b =
  let bLen = blocks bBits 64 in
  let mu = mod_inv_u64 n.[0] in

  let r2 = precomp_r2_mod_n #nLen modBits n in
  let aM = to_mont n mu r2 a in
  let accM = to_mont n mu r2 acc in
  let (aM, accM) = repeati bBits (bn_mod_exp_f #nLen n mu bBits bLen b) (aM, accM) in
  from_mont n mu accM

let bn_mod_exp modBits nLen n a bBits b =
  let acc = bn_from_uint nLen (u64 1) in
  bn_mod_exp_mont modBits nLen n a acc bBits b



val bn_mod_exp_f_lemma:
    #nLen:size_nat{nLen + nLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> bBits:size_pos
  -> bLen:size_nat{bLen == blocks bBits 64}
  -> b:lbignum bLen
  -> i:nat{i < bBits}
  -> aM_accM0: tuple2 (lbignum nLen) (lbignum nLen) -> Lemma
  (requires
   (let (aM0, accM0) = aM_accM0 in
    (1 + (bn_v n % pow2 64) * v mu) % pow2 64 == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    0 < bn_v b /\ bn_v b < pow2 bBits /\
    bn_v aM0 < bn_v n /\ bn_v accM0 < bn_v n))
  (ensures
   (let (aM0, accM0) = aM_accM0 in
    let (aM1, accM1) = bn_mod_exp_f #nLen n mu bBits bLen b i aM_accM0 in
    let (aM2, accM2) = BL.mod_exp_f_ll nLen (bn_v n) (v mu) bBits (bn_v b) i (bn_v aM0, bn_v accM0) in
    bn_v aM1 == aM2 /\ bn_v accM1 == accM2 /\
    bn_v aM1 < bn_v n /\ bn_v accM1 < bn_v n))

let bn_mod_exp_f_lemma #nLen n mu bBits bLen b i (aM0, accM0) =
  let (aM1, accM1) = bn_mod_exp_f #nLen n mu bBits bLen b i (aM0, accM0) in
  let (aM2, accM2) = BL.mod_exp_f_ll nLen (bn_v n) (v mu) bBits (bn_v b) i (bn_v aM0, bn_v accM0) in
  mont_sqr_lemma #nLen n mu aM0;
  assert (bn_v aM1 == aM2);
  bn_is_bit_set_lemma #bLen b i;
  if (bn_v b / pow2 i % 2 = 1) then mont_mul_lemma #nLen n mu aM0 accM0;
  assert (bn_v accM1 == accM2)


val bn_mod_exp_mont_loop_lemma:
    #nLen:size_nat{nLen + nLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> bBits:size_pos
  -> bLen:size_nat{bLen == blocks bBits 64}
  -> b:lbignum bLen
  -> i:size_nat{i <= bBits}
  -> aM_accM0: tuple2 (lbignum nLen) (lbignum nLen) -> Lemma
  (requires
   (let (aM0, accM0) = aM_accM0 in
    (1 + (bn_v n % pow2 64) * v mu) % pow2 64 == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    0 < bn_v b /\ bn_v b < pow2 bBits /\
    bn_v aM0 < bn_v n /\ bn_v accM0 < bn_v n))
  (ensures
   (let (aM0, accM0) = aM_accM0 in
    let (aM1, accM1) = repeati i (bn_mod_exp_f #nLen n mu bBits bLen b) (aM0, accM0) in
    let (aM2, accM2) = repeati i (BL.mod_exp_f_ll nLen (bn_v n) (v mu) bBits (bn_v b)) (bn_v aM0, bn_v accM0) in
    bn_v aM1 == aM2 /\ bn_v accM1 == accM2 /\
    bn_v aM1 < bn_v n /\ bn_v accM1 < bn_v n))

let rec bn_mod_exp_mont_loop_lemma #nLen n mu bBits bLen b i (aM0, accM0) =
  let (aM1, accM1) = repeati i (bn_mod_exp_f #nLen n mu bBits bLen b) (aM0, accM0) in
  let (aM2, accM2) = repeati i (BL.mod_exp_f_ll nLen (bn_v n) (v mu) bBits (bn_v b)) (bn_v aM0, bn_v accM0) in

  if i = 0 then begin
    eq_repeati0 i (bn_mod_exp_f #nLen n mu bBits bLen b) (aM0, accM0);
    eq_repeati0 i (BL.mod_exp_f_ll nLen (bn_v n) (v mu) bBits (bn_v b)) (bn_v aM0, bn_v accM0);
    () end
  else begin
    unfold_repeati i (bn_mod_exp_f #nLen n mu bBits bLen b) (aM0, accM0) (i - 1);
    unfold_repeati i (BL.mod_exp_f_ll nLen (bn_v n) (v mu) bBits (bn_v b)) (bn_v aM0, bn_v accM0) (i - 1);
    let (aM3, accM3) = repeati (i - 1) (bn_mod_exp_f #nLen n mu bBits bLen b) (aM0, accM0) in
    let (aM4, accM4) = repeati (i - 1) (BL.mod_exp_f_ll nLen (bn_v n) (v mu) bBits (bn_v b)) (bn_v aM0, bn_v accM0) in
    assert ((aM1, accM1) == bn_mod_exp_f #nLen n mu bBits bLen b (i - 1) (aM3, accM3));
    assert ((aM2, accM2) == BL.mod_exp_f_ll nLen (bn_v n) (v mu) bBits (bn_v b) (i - 1) (aM4, accM4));
    bn_mod_exp_mont_loop_lemma #nLen n mu bBits bLen b (i - 1) (aM0, accM0);
    assert (bn_v aM3 == aM4 /\ bn_v accM3 == accM4);
    bn_mod_exp_f_lemma #nLen n mu bBits bLen b (i - 1) (aM3, accM3);
    () end


val bn_mod_exp_mont_lemma_aux:
    modBits:size_pos
  -> nLen:size_pos{nLen = (blocks modBits 64) /\ 128 * nLen <= max_size_t}
  -> n:lbignum nLen
  -> a:lbignum nLen
  -> bBits:size_pos
  -> b:lbignum (blocks bBits 64) -> Lemma
  (requires
    bn_v n % 2 = 1 /\ 1 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    0 < bn_v b /\ bn_v b < pow2 bBits /\ bn_v a < bn_v n /\ pow2 (modBits - 1) < bn_v n)
  (ensures
   (let mu = mod_inv_u64 n.[0] in
    let res1 = bn_mod_exp modBits nLen n a bBits b in
    let res2 = BL.mod_exp_mont_ll nLen (bn_v n) (v mu) (bn_v a) bBits (bn_v b) in
    bn_v res1 == res2 /\ bn_v res1 < bn_v n))

let bn_mod_exp_mont_lemma_aux modBits nLen n a bBits b =
  let bLen = blocks bBits 64 in

  let acc = bn_from_uint nLen (u64 1) in
  bn_from_uint_lemma nLen (u64 1);
  assert (bn_v acc == 1);

  let mu = mod_inv_u64 n.[0] in
  bn_eval_index n 0;
  assert (bn_v n % pow2 64 == v n.[0]);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (bn_v n) 2 64;
  assert (v n.[0] % 2 = 1); // since bn_v n % 2 = 1
  mod_inv_u64_lemma n.[0];

  let r2 = precomp_r2_mod_n modBits n in
  precomp_r2_mod_n_lemma modBits n;
  let aM0 = to_mont #nLen n mu r2 a in
  to_mont_lemma #nLen n mu r2 a;

  let accM0 = to_mont #nLen n mu r2 acc in
  to_mont_lemma #nLen n mu r2 acc;

  let (aM1, accM1) = repeati bBits (bn_mod_exp_f #nLen n mu bBits bLen b) (aM0, accM0) in
  bn_mod_exp_mont_loop_lemma #nLen n mu bBits bLen b bBits (aM0, accM0);

  let res = from_mont n mu accM1 in
  from_mont_lemma #nLen n mu accM1


let bn_mod_exp_lemma modBits nLen n a bBits b =
  let mu = mod_inv_u64 n.[0] in
  let r2 = precomp_r2_mod_n modBits n in
  let res1 = bn_mod_exp modBits nLen n a bBits b in
  let res2 = BL.mod_exp_mont_ll nLen (bn_v n) (v mu) (bn_v a) bBits (bn_v b) in
  bn_mod_exp_mont_lemma_aux modBits nLen n a bBits b;
  assert (bn_v res1 == res2 /\ bn_v res1 < bn_v n);

  bn_eval_index n 0;
  assert (bn_v n % pow2 64 == v n.[0]);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (bn_v n) 2 64;
  assert (v n.[0] % 2 = 1); // since bn_v n % 2 = 1
  mod_inv_u64_lemma n.[0];
  assert ((1 + (bn_v n % pow2 64) * v mu) % pow2 64 == 0);

  let d, k = M.eea_pow2_odd (64 * nLen) (bn_v n) in
  M.mont_preconditions nLen (bn_v n) (v mu);
  BL.mod_exp_mont_ll_lemma nLen (bn_v n) d (v mu) (bn_v a) bBits (bn_v b)
