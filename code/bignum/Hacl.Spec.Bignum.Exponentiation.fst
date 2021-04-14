module Hacl.Spec.Bignum.Exponentiation

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions

module LE = Lib.Exponentiation
module SE = Spec.Exponentiation

module E = Hacl.Spec.Exponentiation.Lemmas
module M = Hacl.Spec.Montgomery.Lemmas

module BN = Hacl.Spec.Bignum
module BM = Hacl.Spec.Bignum.Montgomery
module BI = Hacl.Spec.Bignum.ModInvLimb
module ME = Hacl.Spec.Bignum.MontExponentiation
module AE = Hacl.Spec.Bignum.AlmostMontExponentiation

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let bn_check_mod_exp #t #len n a bBits b =
  let pbits = bits t in
  let m0 = BM.bn_check_modulus n in

  bn_eval_bound b (blocks0 bBits pbits);
  let m1 =
    if bBits < pbits * blocks0 bBits pbits then begin
      BN.bn_lt_pow2_mask_lemma b bBits;
      BN.bn_lt_pow2_mask b bBits end
    else begin
      Math.Lemmas.pow2_le_compat bBits (pbits * blocks bBits pbits);
      ones t SEC end in
  assert (if v m1 = 0 then pow2 bBits <= bn_v b else bn_v b < pow2 bBits);

  let m2 = BN.bn_lt_mask a n in
  BN.bn_lt_mask_lemma a n;
  assert (if v m2 = 0 then bn_v a >= bn_v n else bn_v a < bn_v n);

  let m = m1 &. m2 in
  logand_lemma m1 m2;
  let r = m0 &. m in
  logand_lemma m0 m;
  r


val mk_bn_mod_exp_precomp_mont:
    #t:limb_t
  -> len:BN.bn_len t
  -> bn_exp_mont:ME.bn_exp_mont_st t len ->
  bn_mod_exp_precomp_st t len

let mk_bn_mod_exp_precomp_mont #t len bn_exp_mont n mu r2 a bBits b =
  bn_eval_bound n len;
  let aM = BM.bn_to_mont n mu r2 a in
  BM.bn_to_mont_lemma n mu r2 a;

  let accM = bn_exp_mont n mu aM bBits b in

  let acc = BM.bn_from_mont n mu accM in
  BM.bn_from_mont_lemma n mu accM;

  E.mod_exp_mont_ll_lemma (bits t) len (bn_v n) (v mu) (bn_v a) (bn_v b);
  assert (bn_v acc == Lib.NatMod.pow_mod #(bn_v n) (bn_v a) (bn_v b));
  acc


val mk_bn_mod_exp_precomp_amont:
    #t:limb_t
  -> len:BN.bn_len t
  -> bn_exp_almost_mont:AE.bn_exp_almost_mont_st t len ->
  bn_mod_exp_precomp_st t len

let mk_bn_mod_exp_precomp_amont #t len bn_exp_almost_mont n mu r2 a bBits b =
  bn_eval_bound n len;
  let aM = BM.bn_to_mont n mu r2 a in
  BM.bn_to_mont_lemma n mu r2 a;
  M.to_mont_lemma (bits t) len (bn_v n) (v mu) (bn_v a);

  let accM = bn_exp_almost_mont n mu aM bBits b in

  let acc = BM.bn_from_mont n mu accM in
  BM.bn_from_mont_lemma n mu accM;

  bn_eval_bound accM len;
  E.mod_exp_mont_ll_mod_lemma (bits t) len (bn_v n) (v mu) (bn_v a) (bn_v b) (bn_v accM);
  assert (bn_v acc == Lib.NatMod.pow_mod #(bn_v n) (bn_v a) (bn_v b));
  acc


let bn_mod_exp_rl_precomp #t len n mu r2 a bBits b =
  //mk_bn_mod_exp_precomp_mont #t len ME.bn_exp_mont_bm_vartime n mu r2 a bBits b
  mk_bn_mod_exp_precomp_amont #t len AE.bn_exp_almost_mont_bm_vartime n mu r2 a bBits b

let bn_mod_exp_mont_ladder_swap_precomp #t len n mu r2 a bBits b =
  //mk_bn_mod_exp_precomp_mont #t len ME.bn_exp_mont_bm_consttime n mu r2 a bBits b
  mk_bn_mod_exp_precomp_amont #t len AE.bn_exp_almost_mont_bm_consttime n mu r2 a bBits b

let bn_mod_exp_fw_precomp #t len l n mu r2 a bBits b =
  //mk_bn_mod_exp_precomp_mont #t len (ME.bn_exp_mont_fw l) n mu r2 a bBits b
  mk_bn_mod_exp_precomp_amont #t len (AE.bn_exp_almost_mont_fw l) n mu r2 a bBits b


let bn_mod_exp_vartime_precomp #t len n mu r2 a bBits b =
  if bBits < ME.bn_exp_mont_vartime_threshold then
    bn_mod_exp_rl_precomp #t len n mu r2 a bBits b
  else
    bn_mod_exp_fw_precomp #t len 4 n mu r2 a bBits b

let bn_mod_exp_consttime_precomp #t len n mu r2 a bBits b =
  if bBits < ME.bn_exp_mont_consttime_threshold then
    bn_mod_exp_mont_ladder_swap_precomp #t len n mu r2 a bBits b
  else
    bn_mod_exp_fw_precomp #t len 4 n mu r2 a bBits b


val mk_bn_mod_exp_precompr2:
    #t:limb_t
  -> len:BN.bn_len t
  -> bn_exp_precomp:bn_mod_exp_precomp_st t len ->
  bn_mod_exp_precompr2_st t len

let mk_bn_mod_exp_precompr2 #t len bn_exp_precomp n r2 a bBits b =
  let mu = BI.mod_inv_limb n.[0] in
  BI.bn_mod_inv_limb_lemma n;
  bn_exp_precomp n mu r2 a bBits b


let bn_mod_exp_vartime_precompr2 #t len n r2 a bBits b =
  mk_bn_mod_exp_precompr2 #t len (bn_mod_exp_vartime_precomp len) n r2 a bBits b

let bn_mod_exp_consttime_precompr2 #t len n r2 a bBits b =
  mk_bn_mod_exp_precompr2 #t len (bn_mod_exp_consttime_precomp len) n r2 a bBits b


val mk_bn_mod_exp:
    #t:limb_t
  -> len:BN.bn_len t
  -> bn_mod_exp_precomp:bn_mod_exp_precomp_st t len ->
  bn_mod_exp_st t len

let mk_bn_mod_exp #t len bn_mod_exp_precomp nBits n a bBits b =
  let r2, mu = BM.bn_mont_precomp nBits n in
  bn_mod_exp_precomp n mu r2 a bBits b


let bn_mod_exp_vartime #t len nBits n a bBits b =
  mk_bn_mod_exp len (bn_mod_exp_vartime_precomp len) nBits n a bBits b

let bn_mod_exp_consttime #t len nBits n a bBits b =
  mk_bn_mod_exp len (bn_mod_exp_consttime_precomp len) nBits n a bBits b
