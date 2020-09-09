module Hacl.Spec.Bignum.ModReduction

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions

module M = Hacl.Spec.Montgomery.Lemmas
module BM = Hacl.Spec.Bignum.Montgomery
module BI = Hacl.Spec.Bignum.ModInv64

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///
///  Modular reduction based on Montgomery arithmetic (it is slow!)
///

// TODO: we can pass a constant mu as well
val bn_mod_slow_precompr2:
    #nLen:size_pos{128 * nLen <= max_size_t}
  -> n:lbignum nLen
  -> a:lbignum (nLen + nLen)
  -> r2:lbignum nLen ->
  lbignum nLen

let bn_mod_slow_precompr2 #nLen n a r2 =
  let mu = BI.mod_inv_u64 n.[0] in
  let a_mod = BM.mont_reduction n mu a in
  let res = BM.to_mont n mu r2 a_mod in
  res


val bn_mod_slow_precompr2_lemma:
    #nLen:size_pos{128 * nLen <= max_size_t}
  -> n:lbignum nLen
  -> a:lbignum (nLen + nLen)
  -> r2:lbignum nLen -> Lemma
  (requires
    1 < bn_v n /\ bn_v n % 2 = 1 /\ bn_v a < bn_v n * bn_v n /\
    bn_v r2 == pow2 (128 * nLen) % bn_v n)
  (ensures bn_v (bn_mod_slow_precompr2 n a r2) == bn_v a % bn_v n)

let bn_mod_slow_precompr2_lemma #nLen n a r2 =
  let mu = BI.mod_inv_u64 n.[0] in
  bn_eval_index n 0;
  assert (bn_v n % pow2 64 == v n.[0]);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (bn_v n) 2 64;
  assert (v n.[0] % 2 = 1); // since bn_v n % 2 = 1
  BI.mod_inv_u64_lemma n.[0];

  let a_mod = BM.mont_reduction n mu a in
  let res = BM.to_mont n mu r2 a_mod in
  bn_eval_bound n nLen;
  BM.mont_reduction_lemma n mu a;
  BM.to_mont_lemma n mu r2 a_mod;

  let d, k = M.eea_pow2_odd (64 * nLen) (bn_v n) in
  M.mont_preconditions nLen (bn_v n) (v mu);
  M.mont_reduction_lemma nLen (bn_v n) d (v mu) (bn_v a);
  assert (bn_v a_mod == bn_v a * d % bn_v n);
  M.to_mont_lemma nLen (bn_v n) d (v mu) (bn_v a_mod);
  let r = pow2 (64 * nLen) in
  assert (bn_v res == bn_v a_mod * r % bn_v n);
  M.lemma_mont_id1 (bn_v n) r d (bn_v a);
  assert (bn_v res == bn_v a % bn_v n)



val bn_mod_slow:
    #nLen:size_pos{128 * nLen <= max_size_t}
  -> n:lbignum nLen
  -> a:lbignum (nLen + nLen) ->
  lbignum nLen

let bn_mod_slow #nLen n a =
  let r2 = BM.precomp_r2_mod_n n in
  bn_mod_slow_precompr2 #nLen n a r2


val bn_mod_slow_lemma: #nLen:size_pos{128 * nLen <= max_size_t} -> n:lbignum nLen -> a:lbignum (nLen + nLen) -> Lemma
  (requires 1 < bn_v n /\ bn_v n % 2 = 1 /\ bn_v a < bn_v n * bn_v n)
  (ensures  bn_v (bn_mod_slow n a) == bn_v a % bn_v n)

let bn_mod_slow_lemma #nLen n a =
  let r2 = BM.precomp_r2_mod_n n in
  BM.precomp_r2_mod_n_lemma n;
  bn_mod_slow_precompr2_lemma #nLen n a r2
