module Hacl.Spec.Bignum.AlmostMontgomery

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Base
open Hacl.Spec.Bignum.Definitions

module M = Hacl.Spec.Montgomery.Lemmas
module BN = Hacl.Spec.Bignum
module BM = Hacl.Spec.Bignum.Montgomery

friend Hacl.Spec.Bignum.Montgomery

#reset-options "--z3rlimit 100 --fuel 0 --ifuel 0"

///  Low-level specification of Almost Montgomery Multiplication

let bn_almost_mont_reduction #t #nLen n mu c =
  let c0, res = BM.bn_mont_reduction_loop_div_r #t #nLen n mu c in
  let mask = uint #t 0 -. c0 in
  let c1, tmp = BN.bn_sub res n in
  map2 (mask_select mask) tmp res

let bn_almost_mont_mul #t #nLen n mu aM bM =
  let c = BN.bn_mul aM bM in // c = aM * bM
  bn_almost_mont_reduction n mu c // resM = c % n

let bn_almost_mont_sqr #t #nLen n mu aM =
  let c = BN.bn_mul aM aM in // c = aM * aM
  bn_almost_mont_reduction n mu c // resM = c % n


let bn_almost_mont_reduction_lemma #t #nLen n mu res0 =
  let pbits = bits t in
  let r = pow2 (pbits * nLen) in
  let r2 = pow2 (pbits * (nLen + nLen)) in
  Math.Lemmas.pow2_plus (pbits * nLen) (pbits * nLen);
  assert (r2 == r * r);

  let c0, res1 = BM.bn_mont_reduction_loop_div_r #t #nLen n mu res0 in
  let resM1 = M.mont_reduction_loop_div_r (bits t) nLen (bn_v n) (v mu) (bn_v res0) in
  BM.bn_mont_reduction_loop_div_r_lemma #t #nLen n mu res0;
  assert (v c0 * r + bn_v res1 == resM1);

  let resM = if resM1 < r then resM1 else resM1 - bn_v n in
  //assert (resM == AM.almost_mont_reduction (bits t) nLen (bn_v n) (v mu) (bn_v res0));

  let mask = uint #t 0 -. c0 in
  let c1, tmp = BN.bn_sub res1 n in
  BN.bn_sub_lemma res1 n;
  assert (bn_v tmp - v c1 * r == bn_v res1 - bn_v n);

  let res = map2 (mask_select mask) tmp res1 in
  lseq_mask_select_lemma tmp res1 mask;
  assert (res == (if v mask = 0 then res1 else tmp));
  bn_eval_bound res1 nLen;

  M.mont_reduction_loop_div_r_fits_lemma (bits t) nLen (bn_v n) (v mu) (bn_v res0);
  assert (v c0 * r + bn_v res1 <= (bn_v res0 - bn_v n) / r + bn_v n);
  bn_eval_bound res0 (nLen + nLen);
  AM.lemma_fits_c_lt_rr (bn_v res0) r (bn_v n);
  assert (resM1 < r + bn_v n)


let bn_almost_mont_mul_lemma #t #nLen n mu aM bM =
  let r = pow2 (bits t * nLen) in
  let c = BN.bn_mul aM bM in
  BN.bn_mul_lemma aM bM;
  assert (bn_v c == bn_v aM * bn_v bM);
  bn_almost_mont_reduction_lemma n mu c


let bn_almost_mont_sqr_lemma #t #nLen n mu aM =
  bn_almost_mont_mul_lemma #t #nLen n mu aM aM
