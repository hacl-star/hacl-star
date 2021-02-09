module Hacl.Spec.Bignum.Exponentiation

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions

module Loops = Lib.LoopCombinators
module LE = Lib.Exponentiation

module E = Hacl.Spec.Exponentiation.Lemmas
module M = Hacl.Spec.Montgomery.Lemmas

module BN = Hacl.Spec.Bignum
module BM = Hacl.Spec.Bignum.Montgomery
module BI = Hacl.Spec.Bignum.ModInvLimb

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


//////////////////////////////////////////////////////////////////////////

val lemma_bn_mont_pre_is_mont_pre:
    #t:limb_t
  -> #len:size_pos
  -> n:lbignum t len
  -> mu:limb t -> Lemma
  (requires BM.bn_mont_pre n mu)
  (ensures  E.mont_pre (bits t) len (bn_v n) (v mu))

let lemma_bn_mont_pre_is_mont_pre #t #len n mu =
  assert (bn_v n % 2 = 1 /\ 1 < bn_v n);
  bn_eval_bound n len;
  assert (bn_v n < pow2 (bits t * len));
  M.mont_preconditions_n0 (bits t) (bn_v n) (v mu)

unfold
let nat_mod_bn (#t:limb_t) (#len:bn_len t) (n:lbignum t len) =
  x:lbignum t len{bn_v x < bn_v n}


val bn_mont_one:
    #t:limb_t
  -> #len:bn_len t
  -> n:lbignum t len
  -> mu:limb t{BM.bn_mont_pre n mu} ->
  nat_mod_bn n

let bn_mont_one #t #len n mu =
  BM.bn_precomp_r2_mod_n_lemma 0 n;
  let r2 = BM.bn_precomp_r2_mod_n 0 n in
  BM.bn_mont_one_lemma n mu r2;
  BM.bn_mont_one n mu r2


val bn_mont_mul:
    #t:limb_t
  -> #len:bn_len t
  -> n:lbignum t len
  -> mu:limb t{BM.bn_mont_pre n mu}
  -> aM:nat_mod_bn n
  -> bM:nat_mod_bn n ->
  nat_mod_bn n

let bn_mont_mul #t #len n mu aM bM =
  BM.bn_mont_mul_lemma n mu aM bM;
  BM.bn_mont_mul n mu aM bM


val lemma_one_mont_bn:
    #t:limb_t
  -> #len:bn_len t
  -> n:lbignum t len
  -> mu:limb t{BM.bn_mont_pre n mu}
  -> aM:nat_mod_bn n ->
  Lemma (bn_mont_mul n mu aM (bn_mont_one n mu) == aM)

let lemma_one_mont_bn #t #len n mu aM =
  BM.bn_precomp_r2_mod_n_lemma 0 n;
  let r2 = BM.bn_precomp_r2_mod_n 0 n in
  BM.bn_mont_one_lemma n mu r2;
  let oneM = BM.bn_mont_one n mu r2 in
  BM.bn_mont_mul_lemma n mu aM oneM;
  lemma_bn_mont_pre_is_mont_pre #t #len n mu;
  E.lemma_one_mont_ll (bits t) len (bn_v n) (v mu) (bn_v aM);
  bn_eval_inj len (bn_mont_mul n mu aM (bn_mont_one n mu)) aM


val lemma_fmul_assos_mont_bn:
    #t:limb_t
  -> #len:bn_len t
  -> n:lbignum t len
  -> mu:limb t{BM.bn_mont_pre n mu}
  -> aM:nat_mod_bn n
  -> bM:nat_mod_bn n
  -> cM:nat_mod_bn n ->
  Lemma (bn_mont_mul n mu aM (bn_mont_mul n mu bM cM) ==
    bn_mont_mul n mu (bn_mont_mul n mu aM bM) cM)

let lemma_fmul_assos_mont_bn #t #len n mu aM bM cM =
  let rl = bn_mont_mul n mu bM cM in
  BM.bn_mont_mul_lemma n mu bM cM;
  BM.bn_mont_mul_lemma n mu aM rl;

  let rr = bn_mont_mul n mu aM bM in
  BM.bn_mont_mul_lemma n mu aM bM;
  BM.bn_mont_mul_lemma n mu rr cM;
  lemma_bn_mont_pre_is_mont_pre #t #len n mu;
  E.lemma_fmul_assoc_mont_ll (bits t) len (bn_v n) (v mu) (bn_v aM) (bn_v bM) (bn_v cM);
  bn_eval_inj len
    (bn_mont_mul n mu aM (bn_mont_mul n mu bM cM))
    (bn_mont_mul n mu (bn_mont_mul n mu aM bM) cM)


val lemma_fmul_comm_mont_bn:
    #t:limb_t
  -> #len:bn_len t
  -> n:lbignum t len
  -> mu:limb t{BM.bn_mont_pre n mu}
  -> aM:nat_mod_bn n
  -> bM:nat_mod_bn n ->
  Lemma (bn_mont_mul n mu aM bM == bn_mont_mul n mu bM aM)

let lemma_fmul_comm_mont_bn #t #len n mu aM bM =
  BM.bn_mont_mul_lemma n mu aM bM;
  BM.bn_mont_mul_lemma n mu bM aM;
  lemma_bn_mont_pre_is_mont_pre #t #len n mu;
  E.lemma_fmul_comm_mont_ll (bits t) len (bn_v n) (v mu) (bn_v aM) (bn_v bM);
  bn_eval_inj len (bn_mont_mul n mu aM bM) (bn_mont_mul n mu bM aM)


let mk_nat_mont_group_bn
  (#t:limb_t)
  (#len:bn_len t)
  (n:lbignum t len)
  (mu:limb t{BM.bn_mont_pre n mu})
  : LE.exp (nat_mod_bn n) =
{
  LE.one = bn_mont_one #t #len n mu;
  LE.fmul = bn_mont_mul #t #len n mu;
  LE.lemma_one = lemma_one_mont_bn #t #len n mu;
  LE.lemma_fmul_assoc = lemma_fmul_assos_mont_bn #t #len n mu;
  LE.lemma_fmul_comm = lemma_fmul_comm_mont_bn #t #len n mu;
}


val pow_nat_mont_bn_is_pow_nat_mont_ll:
    #t:limb_t
  -> #len:bn_len t
  -> n:lbignum t len
  -> mu:limb t
  -> aM:nat_mod_bn n
  -> b:nat -> Lemma
  (requires
    BM.bn_mont_pre n mu /\
    E.mont_pre (bits t) len (bn_v n) (v mu))
  (ensures
    LE.pow (E.mk_nat_mont_group_ll (bits t) len (bn_v n) (v mu)) (bn_v aM) b ==
    bn_v (LE.pow (mk_nat_mont_group_bn n mu) aM b))

let rec pow_nat_mont_bn_is_pow_nat_mont_ll #t #len n mu aM b =
  let k0 = E.mk_nat_mont_group_ll (bits t) len (bn_v n) (v mu) in
  let k1 = mk_nat_mont_group_bn n mu in
  BM.bn_precomp_r2_mod_n_lemma 0 n;
  let r2 = BM.bn_precomp_r2_mod_n 0 n in

  if b = 0 then begin
    LE.lemma_pow0 k0 (bn_v aM);
    LE.lemma_pow0 k1 aM;
    BM.bn_mont_one_lemma n mu r2 end
  else begin
    LE.lemma_pow_unfold k0 (bn_v aM) b;
    LE.lemma_pow_unfold k1 aM b;
    BM.bn_mont_mul_lemma n mu aM (LE.pow k1 aM (b - 1));
    pow_nat_mont_bn_is_pow_nat_mont_ll #t #len n mu aM (b - 1);
    () end


val bn_mod_exp_mont_pow:
    #t:limb_t
  -> #len:bn_len t
  -> n:lbignum t len
  -> mu:limb t{BM.bn_mont_pre n mu}
  -> a:nat_mod_bn n
  -> bLen:size_nat
  -> b:lbignum t bLen ->
  nat_mod_bn n

let bn_mod_exp_mont_pow #t #len n mu a bLen b =
  BM.bn_precomp_r2_mod_n_lemma 0 n;
  let r2 = BM.bn_precomp_r2_mod_n 0 n in

  let aM = BM.bn_to_mont n mu r2 a in
  BM.bn_to_mont_lemma n mu r2 a;
  let accM = LE.pow (mk_nat_mont_group_bn n mu) aM (bn_v b) in
  //lemma_bn_mont_pre_is_mont_pre #t #len n mu;
  //pow_nat_mont_bn_is_pow_nat_mont_ll #t #len n mu r2 aM (bn_v b);
  let acc = BM.bn_from_mont n mu accM in
  BM.bn_from_mont_lemma n mu accM;
  acc


val bn_mod_exp_mont_pow_lemma:
    #t:limb_t
  -> #len:bn_len t
  -> n:lbignum t len
  -> mu:limb t{BM.bn_mont_pre n mu}
  -> a:nat_mod_bn n
  -> bLen:size_nat
  -> b:lbignum t bLen{0 < bn_v b} ->
  Lemma (bn_v (bn_mod_exp_mont_pow n mu a bLen b) ==
    Lib.NatMod.pow (bn_v a) (bn_v b) % bn_v n)

let bn_mod_exp_mont_pow_lemma #t #len n mu a blen b =
  BM.bn_precomp_r2_mod_n_lemma 0 n;
  let r2 = BM.bn_precomp_r2_mod_n 0 n in

  let aM = BM.bn_to_mont n mu r2 a in
  BM.bn_to_mont_lemma n mu r2 a;
  let accM = LE.pow (mk_nat_mont_group_bn n mu) aM (bn_v b) in
  lemma_bn_mont_pre_is_mont_pre #t #len n mu;
  pow_nat_mont_bn_is_pow_nat_mont_ll #t #len n mu aM (bn_v b);
  let acc = BM.bn_from_mont n mu accM in
  BM.bn_from_mont_lemma n mu accM;
  E.mod_exp_mont_ll_lemma (bits t) len (bn_v n) (v mu) (bn_v a) (bn_v b)

///////////////////////////////////////////////////////////////////////////////

let bn_mod_exp_raw_precompr2 #t len n a bBits b r2 =
  BM.bn_precomp_r2_mod_n_lemma 0 n;
  bn_eval_inj len (BM.bn_precomp_r2_mod_n 0 n) r2;

  let bLen = blocks bBits (bits t) in
  let mu = BI.mod_inv_limb n.[0] in
  BI.bn_mod_inv_limb_lemma n;

  let k = mk_nat_mont_group_bn n mu in

  let aM = BM.bn_to_mont n mu r2 a in
  BM.bn_to_mont_lemma n mu r2 a;
  let accM = LE.exp_rl k aM bBits (bn_v b) in
  LE.exp_rl_lemma k aM bBits (bn_v b);

  let acc = BM.bn_from_mont n mu accM in
  BM.bn_from_mont_lemma n mu accM;
  //assert (acc == bn_mod_exp_mont_pow n mu a bLen b);
  bn_mod_exp_mont_pow_lemma #t #len n mu a bLen b;
  assert (bn_v acc == Lib.NatMod.pow (bn_v a) (bn_v b) % bn_v n);
  Lib.NatMod.lemma_pow_mod #(bn_v n) (bn_v a) (bn_v b);
  acc


let bn_mod_exp_ct_precompr2 #t len n a bBits b r2 =
  BM.bn_precomp_r2_mod_n_lemma 0 n;
  bn_eval_inj len (BM.bn_precomp_r2_mod_n 0 n) r2;

  let bLen = blocks bBits (bits t) in
  let mu = BI.mod_inv_limb n.[0] in
  BI.bn_mod_inv_limb_lemma n;

  let k = mk_nat_mont_group_bn n mu in

  let aM = BM.bn_to_mont n mu r2 a in
  BM.bn_to_mont_lemma n mu r2 a;
  let accM = LE.exp_mont_ladder_swap k aM bBits (bn_v b) in
  LE.exp_mont_ladder_swap_lemma k aM bBits (bn_v b);
  LE.exp_mont_ladder_lemma k aM bBits (bn_v b);

  let acc = BM.bn_from_mont n mu accM in
  BM.bn_from_mont_lemma n mu accM;
  //assert (acc == bn_mod_exp_mont_pow n mu a bLen b);
  bn_mod_exp_mont_pow_lemma #t #len n mu a bLen b;
  assert (bn_v acc == Lib.NatMod.pow (bn_v a) (bn_v b) % bn_v n);
  Lib.NatMod.lemma_pow_mod #(bn_v n) (bn_v a) (bn_v b);
  acc


let bn_mod_exp_fw_precompr2 #t len l n a bBits b r2 =
  BM.bn_precomp_r2_mod_n_lemma 0 n;
  bn_eval_inj len (BM.bn_precomp_r2_mod_n 0 n) r2;

  let bLen = blocks bBits (bits t) in
  let mu = BI.mod_inv_limb n.[0] in
  BI.bn_mod_inv_limb_lemma n;

  let k = mk_nat_mont_group_bn n mu in

  let aM = BM.bn_to_mont n mu r2 a in
  BM.bn_to_mont_lemma n mu r2 a;
  let accM = LE.exp_fw k aM bBits (bn_v b) l in
  LE.exp_fw_lemma k aM bBits (bn_v b) l;

  let acc = BM.bn_from_mont n mu accM in
  BM.bn_from_mont_lemma n mu accM;
  //assert (acc == bn_mod_exp_mont_pow n mu a bLen b);
  bn_mod_exp_mont_pow_lemma #t #len n mu a bLen b;
  assert (bn_v acc == Lib.NatMod.pow (bn_v a) (bn_v b) % bn_v n);
  Lib.NatMod.lemma_pow_mod #(bn_v n) (bn_v a) (bn_v b);
  acc



let bn_mod_exp_raw #t len nBits n a bBits b =
  let r2 = BM.bn_precomp_r2_mod_n nBits n in
  BM.bn_precomp_r2_mod_n_lemma nBits n;
  bn_mod_exp_raw_precompr2 len n a bBits b r2


let bn_mod_exp_ct #t len nBits n a bBits b =
  let r2 = BM.bn_precomp_r2_mod_n nBits n in
  BM.bn_precomp_r2_mod_n_lemma nBits n;
  bn_mod_exp_ct_precompr2 len n a bBits b r2


let bn_mod_exp_fw #t len l nBits n a bBits b =
  let r2 = BM.bn_precomp_r2_mod_n nBits n in
  BM.bn_precomp_r2_mod_n_lemma nBits n;
  bn_mod_exp_fw_precompr2 len l n a bBits b r2
