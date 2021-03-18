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
let bn_mod_t (#t:limb_t) (#len:bn_len t) (n:lbignum t len) =
  x:lbignum t len{bn_v x < bn_v n}


val bn_mont_one:
    #t:limb_t
  -> #len:bn_len t
  -> n:lbignum t len
  -> mu:limb t{BM.bn_mont_pre n mu} ->
  bn_mod_t n

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
  -> aM:bn_mod_t n
  -> bM:bn_mod_t n ->
  bn_mod_t n

let bn_mont_mul #t #len n mu aM bM =
  BM.bn_mont_mul_lemma n mu aM bM;
  BM.bn_mont_mul n mu aM bM


val lemma_bn_mont_one:
    #t:limb_t
  -> #len:bn_len t
  -> n:lbignum t len
  -> mu:limb t{BM.bn_mont_pre n mu}
  -> aM:bn_mod_t n ->
  Lemma (bn_mont_mul n mu aM (bn_mont_one n mu) == aM)

let lemma_bn_mont_one #t #len n mu aM =
  BM.bn_precomp_r2_mod_n_lemma 0 n;
  let r2 = BM.bn_precomp_r2_mod_n 0 n in
  BM.bn_mont_one_lemma n mu r2;
  let oneM = BM.bn_mont_one n mu r2 in
  BM.bn_mont_mul_lemma n mu aM oneM;
  lemma_bn_mont_pre_is_mont_pre #t #len n mu;
  E.lemma_mont_one_ll (bits t) len (bn_v n) (v mu) (bn_v aM);
  bn_eval_inj len (bn_mont_mul n mu aM (bn_mont_one n mu)) aM


val lemma_bn_mont_mul_assoc:
    #t:limb_t
  -> #len:bn_len t
  -> n:lbignum t len
  -> mu:limb t{BM.bn_mont_pre n mu}
  -> aM:bn_mod_t n
  -> bM:bn_mod_t n
  -> cM:bn_mod_t n ->
  Lemma (bn_mont_mul n mu aM (bn_mont_mul n mu bM cM) ==
    bn_mont_mul n mu (bn_mont_mul n mu aM bM) cM)

let lemma_bn_mont_mul_assoc #t #len n mu aM bM cM =
  let rl = bn_mont_mul n mu bM cM in
  BM.bn_mont_mul_lemma n mu bM cM;
  BM.bn_mont_mul_lemma n mu aM rl;

  let rr = bn_mont_mul n mu aM bM in
  BM.bn_mont_mul_lemma n mu aM bM;
  BM.bn_mont_mul_lemma n mu rr cM;
  lemma_bn_mont_pre_is_mont_pre #t #len n mu;
  E.lemma_mont_mul_ll_assoc (bits t) len (bn_v n) (v mu) (bn_v aM) (bn_v bM) (bn_v cM);
  bn_eval_inj len
    (bn_mont_mul n mu aM (bn_mont_mul n mu bM cM))
    (bn_mont_mul n mu (bn_mont_mul n mu aM bM) cM)


val lemma_bn_mont_mul_comm:
    #t:limb_t
  -> #len:bn_len t
  -> n:lbignum t len
  -> mu:limb t{BM.bn_mont_pre n mu}
  -> aM:bn_mod_t n
  -> bM:bn_mod_t n ->
  Lemma (bn_mont_mul n mu aM bM == bn_mont_mul n mu bM aM)

let lemma_bn_mont_mul_comm #t #len n mu aM bM =
  BM.bn_mont_mul_lemma n mu aM bM;
  BM.bn_mont_mul_lemma n mu bM aM;
  lemma_bn_mont_pre_is_mont_pre #t #len n mu;
  E.lemma_mont_mul_ll_comm (bits t) len (bn_v n) (v mu) (bn_v aM) (bn_v bM);
  bn_eval_inj len (bn_mont_mul n mu aM bM) (bn_mont_mul n mu bM aM)


let mk_bn_mont_comm_monoid
  (#t:limb_t)
  (#len:bn_len t)
  (n:lbignum t len)
  (mu:limb t{BM.bn_mont_pre n mu})
  : LE.comm_monoid (bn_mod_t n) =
{
  LE.one = bn_mont_one #t #len n mu;
  LE.mul = bn_mont_mul #t #len n mu;
  LE.lemma_one = lemma_bn_mont_one #t #len n mu;
  LE.lemma_mul_assoc = lemma_bn_mont_mul_assoc #t #len n mu;
  LE.lemma_mul_comm = lemma_bn_mont_mul_comm #t #len n mu;
}


val pow_bn_mont_is_pow_nat_mont_ll:
    #t:limb_t
  -> #len:bn_len t
  -> n:lbignum t len
  -> mu:limb t
  -> aM:bn_mod_t n
  -> b:nat -> Lemma
  (requires
    BM.bn_mont_pre n mu /\
    E.mont_pre (bits t) len (bn_v n) (v mu))
  (ensures
    LE.pow (E.mk_nat_mont_ll_comm_monoid (bits t) len (bn_v n) (v mu)) (bn_v aM) b ==
    bn_v (LE.pow (mk_bn_mont_comm_monoid n mu) aM b))

let rec pow_bn_mont_is_pow_nat_mont_ll #t #len n mu aM b =
  let k0 = E.mk_nat_mont_ll_comm_monoid (bits t) len (bn_v n) (v mu) in
  let k1 = mk_bn_mont_comm_monoid n mu in
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
    pow_bn_mont_is_pow_nat_mont_ll #t #len n mu aM (b - 1);
    () end


val bn_pow_mont:
    #t:limb_t
  -> #len:bn_len t
  -> n:lbignum t len
  -> mu:limb t{BM.bn_mont_pre n mu}
  -> a:bn_mod_t n
  -> bLen:size_nat
  -> b:lbignum t bLen ->
  bn_mod_t n

let bn_pow_mont #t #len n mu a bLen b =
  BM.bn_precomp_r2_mod_n_lemma 0 n;
  let r2 = BM.bn_precomp_r2_mod_n 0 n in

  let aM = BM.bn_to_mont n mu r2 a in
  BM.bn_to_mont_lemma n mu r2 a;
  let accM = LE.pow (mk_bn_mont_comm_monoid n mu) aM (bn_v b) in
  let acc = BM.bn_from_mont n mu accM in
  BM.bn_from_mont_lemma n mu accM;
  acc


val bn_pow_mont_lemma:
    #t:limb_t
  -> #len:bn_len t
  -> n:lbignum t len
  -> mu:limb t{BM.bn_mont_pre n mu}
  -> a:bn_mod_t n
  -> bLen:size_nat
  -> b:lbignum t bLen{0 < bn_v b} ->
  Lemma (bn_v (bn_pow_mont n mu a bLen b) ==
    Lib.NatMod.pow (bn_v a) (bn_v b) % bn_v n)

let bn_pow_mont_lemma #t #len n mu a blen b =
  BM.bn_precomp_r2_mod_n_lemma 0 n;
  let r2 = BM.bn_precomp_r2_mod_n 0 n in

  let aM = BM.bn_to_mont n mu r2 a in
  BM.bn_to_mont_lemma n mu r2 a;
  let accM = LE.pow (mk_bn_mont_comm_monoid n mu) aM (bn_v b) in
  lemma_bn_mont_pre_is_mont_pre #t #len n mu;
  pow_bn_mont_is_pow_nat_mont_ll #t #len n mu aM (bn_v b);
  let acc = BM.bn_from_mont n mu accM in
  BM.bn_from_mont_lemma n mu accM;
  E.mod_exp_mont_ll_lemma (bits t) len (bn_v n) (v mu) (bn_v a) (bn_v b)

///////////////////////////////////////////////////////////////////////////////

let bn_mod_exp_rl_precompr2 #t len n a bBits b r2 =
  BM.bn_precomp_r2_mod_n_lemma 0 n;
  bn_eval_inj len (BM.bn_precomp_r2_mod_n 0 n) r2;

  let bLen = blocks bBits (bits t) in
  let mu = BI.mod_inv_limb n.[0] in
  BI.bn_mod_inv_limb_lemma n;

  let k = mk_bn_mont_comm_monoid n mu in

  let aM = BM.bn_to_mont n mu r2 a in
  BM.bn_to_mont_lemma n mu r2 a;
  let accM = LE.exp_rl k aM bBits (bn_v b) in
  LE.exp_rl_lemma k aM bBits (bn_v b);

  let acc = BM.bn_from_mont n mu accM in
  BM.bn_from_mont_lemma n mu accM;
  //assert (acc == bn_pow_mont n mu a bLen b);
  bn_pow_mont_lemma #t #len n mu a bLen b;
  assert (bn_v acc == Lib.NatMod.pow (bn_v a) (bn_v b) % bn_v n);
  Lib.NatMod.lemma_pow_mod #(bn_v n) (bn_v a) (bn_v b);
  acc


let bn_mod_exp_mont_ladder_swap_precompr2 #t len n a bBits b r2 =
  BM.bn_precomp_r2_mod_n_lemma 0 n;
  bn_eval_inj len (BM.bn_precomp_r2_mod_n 0 n) r2;

  let bLen = blocks bBits (bits t) in
  let mu = BI.mod_inv_limb n.[0] in
  BI.bn_mod_inv_limb_lemma n;

  let k = mk_bn_mont_comm_monoid n mu in

  let aM = BM.bn_to_mont n mu r2 a in
  BM.bn_to_mont_lemma n mu r2 a;
  let accM = LE.exp_mont_ladder_swap k aM bBits (bn_v b) in
  LE.exp_mont_ladder_swap_lemma k aM bBits (bn_v b);
  LE.exp_mont_ladder_lemma k aM bBits (bn_v b);

  let acc = BM.bn_from_mont n mu accM in
  BM.bn_from_mont_lemma n mu accM;
  //assert (acc == bn_pow_mont n mu a bLen b);
  bn_pow_mont_lemma #t #len n mu a bLen b;
  assert (bn_v acc == Lib.NatMod.pow (bn_v a) (bn_v b) % bn_v n);
  Lib.NatMod.lemma_pow_mod #(bn_v n) (bn_v a) (bn_v b);
  acc


let bn_mod_exp_fw_precompr2 #t len l n a bBits b r2 =
  BM.bn_precomp_r2_mod_n_lemma 0 n;
  bn_eval_inj len (BM.bn_precomp_r2_mod_n 0 n) r2;

  let bLen = blocks bBits (bits t) in
  let mu = BI.mod_inv_limb n.[0] in
  BI.bn_mod_inv_limb_lemma n;

  let k = mk_bn_mont_comm_monoid n mu in

  let aM = BM.bn_to_mont n mu r2 a in
  BM.bn_to_mont_lemma n mu r2 a;
  let accM = LE.exp_fw k aM bBits (bn_v b) l in
  LE.exp_fw_lemma k aM bBits (bn_v b) l;

  let acc = BM.bn_from_mont n mu accM in
  BM.bn_from_mont_lemma n mu accM;
  //assert (acc == bn_pow_mont n mu a bLen b);
  bn_pow_mont_lemma #t #len n mu a bLen b;
  assert (bn_v acc == Lib.NatMod.pow (bn_v a) (bn_v b) % bn_v n);
  Lib.NatMod.lemma_pow_mod #(bn_v n) (bn_v a) (bn_v b);
  acc


//TODO: set _threshold properly and
//add `bn_get_window_size` (consttime and vartime)
inline_for_extraction noextract
let bn_mod_exp_vartime_threshold = 200

inline_for_extraction noextract
let bn_mod_exp_consttime_threshold = 200


let bn_mod_exp_vartime_precompr2 #t len n a bBits b r2 =
  if bBits < bn_mod_exp_vartime_threshold then
    bn_mod_exp_rl_precompr2 #t len n a bBits b r2
  else
    bn_mod_exp_fw_precompr2 #t len 4 n a bBits b r2

let bn_mod_exp_consttime_precompr2 #t len n a bBits b r2 =
  if bBits < bn_mod_exp_consttime_threshold then
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
