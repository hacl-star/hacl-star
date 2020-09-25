module Hacl.Spec.Bignum.ModReduction

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions

module M = Hacl.Spec.Montgomery.Lemmas
module BM = Hacl.Spec.Bignum.Montgomery
module BI = Hacl.Spec.Bignum.ModInvLimb
module BN = Hacl.Spec.Bignum

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///
///  Modular reduction based on Montgomery arithmetic (it is slow!)
///

val check_bn_mod:
    #t:limb_t
  -> #nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> n:lbignum t nLen
  -> a:lbignum t (nLen + nLen) ->
  res:limb t{
    let b = 1 < bn_v n && bn_v n % 2 = 1 && bn_v a < bn_v n * bn_v n in
    v res == (if b then v (ones t SEC) else v (zeros t SEC))}

let check_bn_mod #t #nLen n a =
  let m0 = BM.check_modulus n in
  let n2 = BN.bn_mul n n in
  BN.bn_mul_lemma n n;
  let m1 = BN.bn_lt_mask a n2 in
  BN.bn_lt_mask_lemma a n2;
  logand_lemma m0 m1;
  m0 &. m1


// TODO: we can pass a constant mu as well
val bn_mod_slow_precompr2:
    #t:limb_t
  -> #nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> n:lbignum t nLen
  -> a:lbignum t (nLen + nLen)
  -> r2:lbignum t nLen ->
  lbignum t nLen

let bn_mod_slow_precompr2 #t #nLen n a r2 =
  let mu = BI.mod_inv_limb n.[0] in
  let a_mod = BM.mont_reduction n mu a in
  let res = BM.to_mont n mu r2 a_mod in
  res


val bn_mod_slow_precompr2_lemma:
    #t:limb_t
  -> #nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> n:lbignum t nLen
  -> a:lbignum t (nLen + nLen)
  -> r2:lbignum t nLen -> Lemma
  (requires
    1 < bn_v n /\ bn_v n % 2 = 1 /\ bn_v a < bn_v n * bn_v n /\
    bn_v r2 == pow2 (2 * bits t * nLen) % bn_v n)
  (ensures bn_v (bn_mod_slow_precompr2 n a r2) == bn_v a % bn_v n)

let bn_mod_slow_precompr2_lemma #t #nLen n a r2 =
  let mu = BI.mod_inv_limb n.[0] in
  bn_eval_index n 0;
  assert (bn_v n % pow2 (bits t) == v n.[0]);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (bn_v n) 2 (bits t);
  assert (v n.[0] % 2 = 1); // since bn_v n % 2 = 1
  BI.mod_inv_limb_lemma n.[0];

  let a_mod = BM.mont_reduction n mu a in
  let res = BM.to_mont n mu r2 a_mod in
  bn_eval_bound n nLen;
  BM.mont_reduction_lemma n mu a;
  BM.to_mont_lemma n mu r2 a_mod;

  let d, k = M.eea_pow2_odd (bits t * nLen) (bn_v n) in
  M.mont_preconditions (bits t) nLen (bn_v n) (v mu);
  M.mont_reduction_lemma (bits t) nLen (bn_v n) d (v mu) (bn_v a);
  assert (bn_v a_mod == bn_v a * d % bn_v n);
  M.to_mont_lemma (bits t) nLen (bn_v n) d (v mu) (bn_v a_mod);
  let r = pow2 (bits t * nLen) in
  assert (bn_v res == bn_v a_mod * r % bn_v n);
  M.lemma_mont_id1 (bn_v n) r d (bn_v a);
  assert (bn_v res == bn_v a % bn_v n)



val bn_mod_slow:
    #t:limb_t
  -> #nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> n:lbignum t nLen
  -> a:lbignum t (nLen + nLen) ->
  lbignum t nLen

let bn_mod_slow #t #nLen n a =
  let r2 = BM.precomp_r2_mod_n n in
  bn_mod_slow_precompr2 n a r2


val bn_mod_slow_lemma:
    #t:limb_t
  -> #nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> n:lbignum t nLen
  -> a:lbignum t (nLen + nLen) -> Lemma
  (requires 1 < bn_v n /\ bn_v n % 2 = 1 /\ bn_v a < bn_v n * bn_v n)
  (ensures  bn_v (bn_mod_slow n a) == bn_v a % bn_v n)

let bn_mod_slow_lemma #t #nLen n a =
  let r2 = BM.precomp_r2_mod_n n in
  BM.precomp_r2_mod_n_lemma n;
  bn_mod_slow_precompr2_lemma n a r2
