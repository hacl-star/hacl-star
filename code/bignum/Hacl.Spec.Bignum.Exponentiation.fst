module Hacl.Spec.Bignum.Exponentiation

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions

module Loops = Lib.LoopCombinators
module LE = Lib.Exponentiation
module SE = Spec.Exponentiation

module E = Hacl.Spec.Exponentiation.Lemmas
module M = Hacl.Spec.Montgomery.Lemmas

module BN = Hacl.Spec.Bignum
module BM = Hacl.Spec.Bignum.Montgomery
module BI = Hacl.Spec.Bignum.ModInvLimb
module ME = Hacl.Spec.Bignum.MontExponentiation

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let bn_check_mod_exp #t #len n a bBits b =
  let pbits = bits t in
  let m0 = BM.bn_check_modulus n in
  let m1 = BN.bn_is_zero_mask b in
  BN.bn_is_zero_mask_lemma b;
  assert (if v m1 = 0 then bn_v b > 0 else bn_v b = 0);
  assert (v m1 = 0 \/ v m1 = ones_v t);
  let m1' = lognot m1 in
  lognot_lemma m1;
  assert (if v m1' = 0 then bn_v b = 0 else bn_v b > 0);

  bn_eval_bound b (blocks bBits pbits);
  let m2 =
    if bBits < pbits * blocks bBits pbits then begin
      BN.bn_lt_pow2_mask_lemma b bBits;
      BN.bn_lt_pow2_mask b bBits end
    else begin
      Math.Lemmas.pow2_le_compat bBits (pbits * blocks bBits pbits);
      ones t SEC end in
  assert (if v m2 = 0 then pow2 bBits <= bn_v b else bn_v b < pow2 bBits);

  let m3 = BN.bn_lt_mask a n in
  BN.bn_lt_mask_lemma a n;
  assert (if v m3 = 0 then bn_v a >= bn_v n else bn_v a < bn_v n);

  let m = m1' &. m2 &. m3 in
  logand_ones (m1' &. m2);
  logand_zeros (m1' &. m2);
  logand_ones m1';
  logand_zeros m1';
  let r = m0 &. m in
  logand_lemma m0 m;
  r


let bn_mod_exp_rl_precompr2 #t len n a bBits b r2 =
  let bLen = blocks bBits (bits t) in
  let mu = BI.mod_inv_limb n.[0] in
  BI.bn_mod_inv_limb_lemma n;
  bn_eval_bound n len;

  let k1 = ME.mk_bn_mont_concrete_ops n mu in

  let aM = BM.bn_to_mont n mu r2 a in
  BM.bn_to_mont_lemma n mu r2 a;

  let accM = SE.exp_rl k1 aM bBits (bn_v b) in
  LE.exp_rl_lemma k1.SE.to.SE.comm_monoid (bn_v aM) bBits (bn_v b);

  let acc = BM.bn_from_mont n mu accM in
  BM.bn_from_mont_lemma n mu accM;

  E.mod_exp_mont_ll_lemma (bits t) len (bn_v n) (v mu) (bn_v a) (bn_v b);
  assert (bn_v acc == Lib.NatMod.pow_mod #(bn_v n) (bn_v a) (bn_v b));
  acc


let bn_mod_exp_mont_ladder_swap_precompr2 #t len n a bBits b r2 =
  let bLen = blocks bBits (bits t) in
  let mu = BI.mod_inv_limb n.[0] in
  BI.bn_mod_inv_limb_lemma n;
  bn_eval_bound n len;

  let k1 = ME.mk_bn_mont_concrete_ops n mu in

  let aM = BM.bn_to_mont n mu r2 a in
  BM.bn_to_mont_lemma n mu r2 a;

  let accM = SE.exp_mont_ladder_swap k1 aM bBits (bn_v b) in
  LE.exp_mont_ladder_swap_lemma k1.SE.to.SE.comm_monoid (bn_v aM) bBits (bn_v b);
  LE.exp_mont_ladder_lemma k1.SE.to.SE.comm_monoid (bn_v aM) bBits (bn_v b);

  let acc = BM.bn_from_mont n mu accM in
  BM.bn_from_mont_lemma n mu accM;

  E.mod_exp_mont_ll_lemma (bits t) len (bn_v n) (v mu) (bn_v a) (bn_v b);
  assert (bn_v acc == Lib.NatMod.pow_mod #(bn_v n) (bn_v a) (bn_v b));
  acc


let bn_mod_exp_fw_precompr2 #t len l n a bBits b r2 =
  let bLen = blocks bBits (bits t) in
  let mu = BI.mod_inv_limb n.[0] in
  BI.bn_mod_inv_limb_lemma n;
  bn_eval_bound n len;

  let k1 = ME.mk_bn_mont_concrete_ops n mu in

  let aM = BM.bn_to_mont n mu r2 a in
  BM.bn_to_mont_lemma n mu r2 a;

  let accM = SE.exp_fw k1 aM bBits (bn_v b) l in
  LE.exp_fw_lemma k1.SE.to.SE.comm_monoid (bn_v aM) bBits (bn_v b) l;

  let acc = BM.bn_from_mont n mu accM in
  BM.bn_from_mont_lemma n mu accM;

  E.mod_exp_mont_ll_lemma (bits t) len (bn_v n) (v mu) (bn_v a) (bn_v b);
  assert (bn_v acc == Lib.NatMod.pow_mod #(bn_v n) (bn_v a) (bn_v b));
  acc


let bn_mod_exp_vartime_precompr2 #t len n a bBits b r2 =
  if bBits < ME.bn_exp_mont_vartime_threshold then
    bn_mod_exp_rl_precompr2 #t len n a bBits b r2
  else
    bn_mod_exp_fw_precompr2 #t len 4 n a bBits b r2

let bn_mod_exp_consttime_precompr2 #t len n a bBits b r2 =
  if bBits < ME.bn_exp_mont_consttime_threshold then
    bn_mod_exp_mont_ladder_swap_precompr2 #t len n a bBits b r2
  else
    bn_mod_exp_fw_precompr2 #t len 4 n a bBits b r2


let bn_mod_exp_vartime #t len nBits n a bBits b =
  let r2 = BM.bn_precomp_r2_mod_n nBits n in
  BM.bn_precomp_r2_mod_n_lemma nBits n;
  bn_mod_exp_vartime_precompr2 #t len n a bBits b r2


let bn_mod_exp_consttime #t len nBits n a bBits b =
  let r2 = BM.bn_precomp_r2_mod_n nBits n in
  BM.bn_precomp_r2_mod_n_lemma nBits n;
  bn_mod_exp_consttime_precompr2 #t len n a bBits b r2
