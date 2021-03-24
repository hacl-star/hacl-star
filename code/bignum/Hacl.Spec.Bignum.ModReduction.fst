module Hacl.Spec.Bignum.ModReduction

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions

module M = Hacl.Spec.Montgomery.Lemmas
module AM = Hacl.Spec.AlmostMontgomery.Lemmas

module BM = Hacl.Spec.Bignum.Montgomery
module BAM = Hacl.Spec.Bignum.AlmostMontgomery

module BI = Hacl.Spec.Bignum.ModInvLimb
module BN = Hacl.Spec.Bignum

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///  Modular reduction based on Montgomery arithmetic

val bn_mod_slow_precompr2:
    #t:limb_t
  -> #nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> r2:lbignum t nLen
  -> a:lbignum t (nLen + nLen) ->
  lbignum t nLen

let bn_mod_slow_precompr2 #t #nLen n mu r2 a =
  let a_mod = BAM.bn_almost_mont_reduction n mu a in
  let res = BM.bn_to_mont n mu r2 a_mod in
  res


val bn_mod_slow_precompr2_lemma:
    #t:limb_t
  -> #nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> r2:lbignum t nLen
  -> a:lbignum t (nLen + nLen) -> Lemma
  (requires
    BM.bn_mont_pre n mu /\
    bn_v r2 == pow2 (2 * bits t * nLen) % bn_v n)
  (ensures bn_v (bn_mod_slow_precompr2 n mu r2 a) == bn_v a % bn_v n)

let bn_mod_slow_precompr2_lemma #t #nLen n mu r2 a =
  let r = pow2 (bits t * nLen) in
  let d, _ = M.eea_pow2_odd (bits t * nLen) (bn_v n) in
  M.mont_preconditions_d (bits t) nLen (bn_v n);
  assert (M.mont_pre (bits t) nLen (bn_v n) (v mu));

  let a_mod = BAM.bn_almost_mont_reduction n mu a in
  let res = BM.bn_to_mont n mu r2 a_mod in
  BAM.bn_almost_mont_reduction_lemma n mu a;
  BM.bn_to_mont_lemma n mu r2 a_mod;

  bn_eval_bound a (nLen + nLen);
  assert (bn_v a < pow2 (bits t * (nLen + nLen)));
  Math.Lemmas.pow2_plus (bits t * nLen) (bits t * nLen);
  assert (bn_v a < r * r);

  AM.almost_mont_reduction_lemma (bits t) nLen (bn_v n) d (v mu) (bn_v a);
  assert (bn_v a_mod % bn_v n == bn_v a * d % bn_v n);

  calc (==) {
    bn_v res;
    (==) { M.to_mont_lemma (bits t) nLen (bn_v n) d (v mu) (bn_v a_mod) }
    bn_v a_mod * r % bn_v n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (bn_v a_mod) r (bn_v n) }
    bn_v a_mod % bn_v n * r % bn_v n;
    (==) {  }
    (bn_v a * d % bn_v n) * r % bn_v n;
    (==) { M.lemma_mont_id1 (bn_v n) r d (bn_v a) }
    bn_v a % bn_v n;
    };

  assert (bn_v res == bn_v a % bn_v n)


val bn_mod_slow:
    #t:limb_t
  -> #nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> nBits:size_nat{nBits / bits t < nLen}
  -> n:lbignum t nLen
  -> a:lbignum t (nLen + nLen) ->
  lbignum t nLen

let bn_mod_slow #t #nLen nBits n a =
  let mu = BI.mod_inv_limb n.[0] in
  let r2 = BM.bn_precomp_r2_mod_n nBits n in
  bn_mod_slow_precompr2 n mu r2 a


val bn_mod_slow_lemma:
    #t:limb_t
  -> #nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> nBits:size_nat{nBits / bits t < nLen}
  -> n:lbignum t nLen
  -> a:lbignum t (nLen + nLen) -> Lemma
  (requires
    1 < bn_v n /\ bn_v n % 2 = 1 /\
    pow2 nBits < bn_v n)
  (ensures  bn_v (bn_mod_slow nBits n a) == bn_v a % bn_v n)

let bn_mod_slow_lemma #t #nLen nBits n a =
  let mu = BI.mod_inv_limb n.[0] in
  BI.bn_mod_inv_limb_lemma n;
  let r2 = BM.bn_precomp_r2_mod_n nBits n in
  BM.bn_precomp_r2_mod_n_lemma nBits n;
  bn_eval_bound n nLen;
  bn_mod_slow_precompr2_lemma n mu r2 a
