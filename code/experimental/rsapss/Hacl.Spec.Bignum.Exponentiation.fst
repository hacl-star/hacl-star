module Hacl.Spec.Bignum.Exponentiation

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.LoopCombinators

open Hacl.Spec.Bignum
open Hacl.Spec.Bignum.Base
open Hacl.Spec.Bignum.Montgomery
open Hacl.Spec.Bignum.Montgomery.PreCompConstants


module M = Hacl.Spec.Bignum.Montgomery.Lemmas
module BL = Hacl.Spec.Bignum.Lemmas

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val bn_is_bit_set: #len:size_nat -> input:lbignum len -> ind:size_nat{ind / 64 < len} -> bool
let bn_is_bit_set #len input ind =
  let i = ind / 64 in
  let j = ind % 64 in
  let tmp = input.[i] in
  let tmp = (tmp >>. size j) &. u64 1 in
  eq_u64 tmp (u64 1)


val bn_is_bit_set_lemma: #len:size_nat -> b:lbignum len -> i:size_nat{i / 64 < len} -> Lemma
  ((bn_v b / pow2 i % 2 = 1) == bn_is_bit_set #len b i)
let bn_is_bit_set_lemma #len b i = admit()


val mod_exp_f:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> bBits:size_pos
  -> bLen:size_nat{bLen == blocks bBits 64}
  -> b:lbignum bLen
  -> i:nat{i < bBits}
  -> aM_accM: tuple2 (lbignum rLen) (lbignum rLen) ->
  tuple2 (lbignum rLen) (lbignum rLen)

let mod_exp_f #nLen #rLen n nInv_u64 bBits bLen b i aM_accM =
  let (aM, accM) = aM_accM in
  let accM = if (bn_is_bit_set #bLen b i) then mul_mod_mont n nInv_u64 aM accM else accM in // acc = (acc * a) % n
  let aM = mul_mod_mont n nInv_u64 aM aM in // a = (a * a) % n
  (aM, accM)


val mod_exp:
    modBits:size_pos
  -> nLen:size_pos{nLen = (blocks modBits 64) /\ 128 * (nLen + 1) <= max_size_t}
  -> n:lbignum nLen
  -> r2:lbignum nLen
  -> a:lbignum nLen
  -> bBits:size_pos
  -> b:lbignum (blocks bBits 64) ->
  res:lbignum nLen

let mod_exp modBits nLen n r2 a bBits b =
  let rLen = nLen + 1 in
  let bLen = blocks bBits 64 in

  let acc  = create nLen (u64 0) in
  let acc = acc.[0] <- u64 1 in
  let nInv_u64 = mod_inv_u64 n.[0] in

  let aM = to_mont n nInv_u64 r2 a in
  let accM = to_mont n nInv_u64 r2 acc in
  let (aM, accM) = repeati bBits (mod_exp_f #nLen #rLen n nInv_u64 bBits bLen b) (aM, accM) in
  from_mont n nInv_u64 accM


val mod_exp_f_lemma:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> bBits:size_pos
  -> bLen:size_nat{bLen == blocks bBits 64}
  -> b:lbignum bLen
  -> i:nat{i < bBits}
  -> aM_accM0: tuple2 (lbignum rLen) (lbignum rLen) -> Lemma
  (requires
   (let (aM0, accM0) = aM_accM0 in
    (1 + (bn_v n % pow2 64) * v mu) % pow2 64 == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    0 < bn_v b /\ bn_v b < pow2 bBits /\
    bn_v aM0 < 2 * bn_v n /\ bn_v accM0 < 2 * bn_v n))
  (ensures
   (let (aM0, accM0) = aM_accM0 in
    let (aM1, accM1) = mod_exp_f #nLen #rLen n mu bBits bLen b i aM_accM0 in
    let (aM2, accM2) = BL.mod_exp_f_ll rLen (bn_v n) (v mu) bBits (bn_v b) i (bn_v aM0, bn_v accM0) in
    bn_v aM1 == aM2 /\ bn_v accM1 == accM2 /\
    bn_v aM1 < 2 * bn_v n /\ bn_v accM1 < 2 * bn_v n))

let mod_exp_f_lemma #nLen #rLen n mu bBits bLen b i (aM0, accM0) =
  let (aM1, accM1) = mod_exp_f #nLen #rLen n mu bBits bLen b i (aM0, accM0) in
  let (aM2, accM2) = BL.mod_exp_f_ll rLen (bn_v n) (v mu) bBits (bn_v b) i (bn_v aM0, bn_v accM0) in
  mul_mod_mont_lemma #nLen #rLen n mu aM0 aM0;
  assert (bn_v aM1 == aM2);
  bn_is_bit_set_lemma #bLen b i;
  if (bn_v b / pow2 i % 2 = 1) then mul_mod_mont_lemma #nLen #rLen n mu aM0 accM0;
  assert (bn_v accM1 == accM2);
  let d, k = BL.eea_pow2_odd (64 * rLen) (bn_v n) in
  BL.mod_exp_mont_preconditions rLen (bn_v n) (v mu);
  BL.mod_exp_mont_preconditions_rLen nLen (bn_v n);
  BL.mod_exp_mont_ll_lemma_fits_loop_step rLen (bn_v n) d (v mu) bBits (bn_v b) i (bn_v aM0) (bn_v accM0)


val mod_exp_mont_loop_lemma:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> bBits:size_pos
  -> bLen:size_nat{bLen == blocks bBits 64}
  -> b:lbignum bLen
  -> i:size_nat{i <= bBits}
  -> aM_accM0: tuple2 (lbignum rLen) (lbignum rLen) -> Lemma
  (requires
   (let (aM0, accM0) = aM_accM0 in
    (1 + (bn_v n % pow2 64) * v mu) % pow2 64 == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    0 < bn_v b /\ bn_v b < pow2 bBits /\
    bn_v aM0 < 2 * bn_v n /\ bn_v accM0 < 2 * bn_v n))
  (ensures
   (let (aM0, accM0) = aM_accM0 in
    let (aM1, accM1) = repeati i (mod_exp_f #nLen #rLen n mu bBits bLen b) (aM0, accM0) in
    let (aM2, accM2) = repeati i (BL.mod_exp_f_ll rLen (bn_v n) (v mu) bBits (bn_v b)) (bn_v aM0, bn_v accM0) in
    bn_v aM1 == aM2 /\ bn_v accM1 == accM2 /\
    bn_v aM1 < 2 * bn_v n /\ bn_v accM1 < 2 * bn_v n))

let rec mod_exp_mont_loop_lemma #nLen #rLen n mu bBits bLen b i (aM0, accM0) =
  let (aM1, accM1) = repeati i (mod_exp_f #nLen #rLen n mu bBits bLen b) (aM0, accM0) in
  let (aM2, accM2) = repeati i (BL.mod_exp_f_ll rLen (bn_v n) (v mu) bBits (bn_v b)) (bn_v aM0, bn_v accM0) in

  if i = 0 then begin
    eq_repeati0 i (mod_exp_f #nLen #rLen n mu bBits bLen b) (aM0, accM0);
    eq_repeati0 i (BL.mod_exp_f_ll rLen (bn_v n) (v mu) bBits (bn_v b)) (bn_v aM0, bn_v accM0);
    () end
  else begin
    unfold_repeati i (mod_exp_f #nLen #rLen n mu bBits bLen b) (aM0, accM0) (i - 1);
    unfold_repeati i (BL.mod_exp_f_ll rLen (bn_v n) (v mu) bBits (bn_v b)) (bn_v aM0, bn_v accM0) (i - 1);
    let (aM3, accM3) = repeati (i - 1) (mod_exp_f #nLen #rLen n mu bBits bLen b) (aM0, accM0) in
    let (aM4, accM4) = repeati (i - 1) (BL.mod_exp_f_ll rLen (bn_v n) (v mu) bBits (bn_v b)) (bn_v aM0, bn_v accM0) in
    assert ((aM1, accM1) == mod_exp_f #nLen #rLen n mu bBits bLen b (i - 1) (aM3, accM3));
    assert ((aM2, accM2) == BL.mod_exp_f_ll rLen (bn_v n) (v mu) bBits (bn_v b) (i - 1) (aM4, accM4));
    mod_exp_mont_loop_lemma #nLen #rLen n mu bBits bLen b (i - 1) (aM0, accM0);
    assert (bn_v aM3 == aM4 /\ bn_v accM3 == accM4);
    mod_exp_f_lemma #nLen #rLen n mu bBits bLen b (i - 1) (aM3, accM3);
    () end


val mod_exp_mont_lemma:
    modBits:size_pos
  -> nLen:size_pos{nLen = (blocks modBits 64) /\ 128 * (nLen + 1) <= max_size_t}
  -> n:lbignum nLen
  -> r2:lbignum nLen
  -> a:lbignum nLen
  -> bBits:size_pos
  -> b:lbignum (blocks bBits 64) -> Lemma
  (requires
   (bn_v n % 2 = 1 /\ 1 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    0 < bn_v b /\ bn_v b < pow2 bBits /\ bn_v a < bn_v n /\
    bn_v r2 == pow2 (128 * (nLen + 1)) % bn_v n))
  (ensures
   (let mu = mod_inv_u64 n.[0] in
    let res1 = mod_exp modBits nLen n r2 a bBits b in
    let res2 = BL.mod_exp_mont_ll_final_sub (nLen + 1) (bn_v n) (v mu) (bn_v a) bBits (bn_v b) in
    bn_v res1 == res2 /\ bn_v res1 < bn_v n))

let mod_exp_mont_lemma modBits nLen n r2 a bBits b =
  let rLen = nLen + 1 in
  let bLen = blocks bBits 64 in

  let acc  = create nLen (u64 0) in
  let acc = acc.[0] <- u64 1 in
  assume (bn_v acc == 1);

  let mu = mod_inv_u64 n.[0] in
  assume (v n.[0] % 2 = 1); // since bn_v n % 2 = 1
  assume (bn_v n % pow2 64 == v n.[0]);
  mod_inv_u64_lemma n.[0];

  let aM0 = to_mont #nLen #rLen n mu r2 a in
  to_mont_lemma #nLen #rLen n mu r2 a;

  let accM0 = to_mont #nLen #rLen n mu r2 acc in
  to_mont_lemma #nLen #rLen n mu r2 acc;

  let (aM1, accM1) = repeati bBits (mod_exp_f #nLen #rLen n mu bBits bLen b) (aM0, accM0) in
  mod_exp_mont_loop_lemma #nLen #rLen n mu bBits bLen b bBits (aM0, accM0);

  let res = from_mont n mu accM1 in
  from_mont_lemma #nLen #rLen n mu accM1;
  assert (bn_v res == BL.mod_exp_mont_ll rLen (bn_v n) (v mu) (bn_v a) bBits (bn_v b));
  assert (bn_v res <= bn_v n);
  admit() // TODO: add a final conditional substraction
