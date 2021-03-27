module Hacl.Bignum.Exponentiation

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions

module ST = FStar.HyperStack.ST

module BD = Hacl.Spec.Bignum.Definitions
module SM = Hacl.Spec.Bignum.Montgomery

module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery
module ME = Hacl.Bignum.MontExponentiation

module E = Hacl.Spec.Exponentiation.Lemmas
module SE = Hacl.Spec.Bignum.MontExponentiation
module S = Hacl.Spec.Bignum.Exponentiation

friend Hacl.Spec.Bignum.Exponentiation
friend Hacl.Bignum.Montgomery

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let bn_check_mod_exp #t len n a bBits b =
  let m0 = BM.bn_check_modulus n in
  let bLen = blocks bBits (size (bits t)) in
  let m1 = BN.bn_is_zero_mask bLen b in
  let m1' = lognot m1 in
  let m2 =
    if bBits <. size (bits t) *! bLen
    then BN.bn_lt_pow2_mask bLen b bBits
    else ones t SEC in
  let m3 = BN.bn_lt_mask len a n in
  let m = m1' &. m2 &. m3 in
  m0 &. m


inline_for_extraction noextract
val mk_bn_mod_exp_precomp:
    #t:limb_t
  -> k:BM.mont t
  -> bn_exp_mont: ME.bn_exp_mont_st t k.BM.bn.BN.len ->
  bn_mod_exp_precomp_st t k.BM.bn.BN.len

let mk_bn_mod_exp_precomp #t k bn_exp_mont n mu r2 a bBits b res =
  let h0 = ST.get () in
  [@inline_let] let len = k.BM.bn.BN.len in
  push_frame ();
  BD.bn_eval_bound (as_seq h0 n) (v len);
  let aM = create len (uint #t #SEC 0) in
  BM.to n mu r2 a aM;
  SM.bn_to_mont_lemma (as_seq h0 n) mu (as_seq h0 r2) (as_seq h0 a);

  let resM = create len (uint #t #SEC 0) in
  bn_exp_mont n mu r2 aM bBits b resM;
  BM.from n mu resM res;

  let h1 = ST.get () in
  SM.bn_from_mont_lemma (as_seq h0 n) mu (as_seq h1 resM);
  E.mod_exp_mont_ll_lemma (bits t) (v len) (bn_v h0 n) (v mu) (bn_v h0 a) (bn_v h0 b);
  assert (bn_v h1 res == Lib.NatMod.pow_mod #(bn_v h0 n) (bn_v h0 a) (bn_v h0 b));
  pop_frame ()


let bn_mod_exp_bm_vartime_precomp #t k n mu r2 a bBits b res =
  mk_bn_mod_exp_precomp #t k (ME.bn_exp_mont_bm_vartime #t k) n mu r2 a bBits b res

let bn_mod_exp_bm_consttime_precomp #t k n mu r2 a bBits b res =
  mk_bn_mod_exp_precomp #t k (ME.bn_exp_mont_bm_consttime #t k) n mu r2 a bBits b res

let bn_mod_exp_fw_vartime_precomp #t k l n mu r2 a bBits b res =
  mk_bn_mod_exp_precomp #t k (ME.bn_exp_mont_fw_vartime #t k l) n mu r2 a bBits b res

let bn_mod_exp_fw_consttime_precomp #t k l n mu r2 a bBits b res =
  mk_bn_mod_exp_precomp #t k (ME.bn_exp_mont_fw_consttime #t k l) n mu r2 a bBits b res


let bn_mod_exp_consttime_precomp #t len bn_mod_exp_bm_consttime_precomp bn_mod_exp_fw_consttime_precomp n mu r2 a bBits b res =
  if bBits <. size SE.bn_exp_mont_consttime_threshold then
    bn_mod_exp_bm_consttime_precomp n mu r2 a bBits b res
  else
    bn_mod_exp_fw_consttime_precomp n mu r2 a bBits b res


let bn_mod_exp_vartime_precomp #t len bn_mod_exp_bm_vartime_precomp bn_mod_exp_fw_vartime_precomp n mu r2 a bBits b res =
  if bBits <. size SE.bn_exp_mont_vartime_threshold then
    bn_mod_exp_bm_vartime_precomp n mu r2 a bBits b res
  else
    bn_mod_exp_fw_vartime_precomp n mu r2 a bBits b res


let mk_bn_mod_exp_precompr2 #t k bn_mod_exp_precomp n r2 a bBits b res =
  let h0 = ST.get () in
  let mu = BM.mod_inv_limb n.(0ul) in // n * mu = 1 (mod (pow2 64))
  Hacl.Spec.Bignum.ModInvLimb.bn_mod_inv_limb_lemma (as_seq h0 n);
  bn_mod_exp_precomp n mu r2 a bBits b res


let mk_bn_mod_exp #t len precomp_r2 bn_mod_exp_precomp nBits n a bBits b res =
  let h0 = ST.get () in
  SM.bn_precomp_r2_mod_n_lemma (v nBits) (as_seq h0 n);
  push_frame ();
  let r2 = create len (uint #t #SEC 0) in
  precomp_r2 nBits n r2;
  let mu = BM.mod_inv_limb n.(0ul) in // n * mu = 1 (mod (pow2 64))
  Hacl.Spec.Bignum.ModInvLimb.bn_mod_inv_limb_lemma (as_seq h0 n);
  bn_mod_exp_precomp n mu r2 a bBits b res;
  pop_frame ()

///////////////////////////////////////////////

/// A fully runtime implementation of modular exponentiation.

let bn_check_mod_exp_u32 (len:BN.meta_len U32) : bn_check_mod_exp_st U32 len =
  bn_check_mod_exp len
let bn_mod_exp_vartime_precomp_u32 (len:BN.meta_len U32) : bn_mod_exp_precomp_st U32 len =
  [@inline_let]
  let km = BM.mk_runtime_mont len in
  bn_mod_exp_vartime_precomp len
    (bn_mod_exp_bm_vartime_precomp km)
    (bn_mod_exp_fw_vartime_precomp km 4ul)
let bn_mod_exp_consttime_precomp_u32 (len:BN.meta_len U32) : bn_mod_exp_precomp_st U32 len =
  [@inline_let]
  let km = BM.mk_runtime_mont len in
  bn_mod_exp_consttime_precomp len
    (bn_mod_exp_bm_consttime_precomp km)
    (bn_mod_exp_fw_consttime_precomp km 4ul)
let bn_mod_exp_vartime_u32 (len:BN.meta_len U32) : bn_mod_exp_st U32 len =
  mk_bn_mod_exp len (BM.bn_precomp_r2_mod_n_u32 len) (bn_mod_exp_vartime_precomp_u32 len)
let bn_mod_exp_consttime_u32 (len:BN.meta_len U32) : bn_mod_exp_st U32 len =
  mk_bn_mod_exp len (BM.bn_precomp_r2_mod_n_u32 len) (bn_mod_exp_consttime_precomp_u32 len)


inline_for_extraction noextract
let mk_runtime_exp_u32 (len:BN.meta_len U32) : exp U32 = {
  bn = BN.mk_runtime_bn U32 len;
  mod_check = BM.bn_check_modulus;
  exp_check = bn_check_mod_exp_u32 len;
  precompr2 = BM.bn_precomp_r2_mod_n_u32 len;
  exp_vt_precomp = bn_mod_exp_vartime_precomp_u32 len;
  exp_ct_precomp = bn_mod_exp_consttime_precomp_u32 len;
  exp_vt = bn_mod_exp_vartime_u32 len;
  exp_ct = bn_mod_exp_consttime_u32 len;
  }


let bn_check_mod_exp_u64 (len:BN.meta_len U64) : bn_check_mod_exp_st U64 len =
  bn_check_mod_exp len
let bn_mod_exp_vartime_precomp_u64 (len:BN.meta_len U64) : bn_mod_exp_precomp_st U64 len =
  [@inline_let]
  let km = BM.mk_runtime_mont len in
  bn_mod_exp_vartime_precomp len
    (bn_mod_exp_bm_vartime_precomp km)
    (bn_mod_exp_fw_vartime_precomp km 4ul)
let bn_mod_exp_consttime_precomp_u64 (len:BN.meta_len U64) : bn_mod_exp_precomp_st U64 len =
  [@inline_let]
  let km = BM.mk_runtime_mont len in
  bn_mod_exp_consttime_precomp len
    (bn_mod_exp_bm_consttime_precomp km)
    (bn_mod_exp_fw_consttime_precomp km 4ul)
let bn_mod_exp_vartime_u64 (len:BN.meta_len U64) : bn_mod_exp_st U64 len =
  mk_bn_mod_exp len (BM.bn_precomp_r2_mod_n_u64 len) (bn_mod_exp_vartime_precomp_u64 len)
let bn_mod_exp_consttime_u64 (len:BN.meta_len U64) : bn_mod_exp_st U64 len =
  mk_bn_mod_exp len (BM.bn_precomp_r2_mod_n_u64 len) (bn_mod_exp_consttime_precomp_u64 len)


inline_for_extraction noextract
let mk_runtime_exp_u64 (len:BN.meta_len U64) : exp U64 = {
  bn = BN.mk_runtime_bn U64 len;
  mod_check = BM.bn_check_modulus;
  exp_check = bn_check_mod_exp_u64 len;
  precompr2 = BM.bn_precomp_r2_mod_n_u64 len;
  exp_vt_precomp = bn_mod_exp_vartime_precomp_u64 len;
  exp_ct_precomp = bn_mod_exp_consttime_precomp_u64 len;
  exp_vt = bn_mod_exp_vartime_u64 len;
  exp_ct = bn_mod_exp_consttime_u64 len;
  }


let mk_runtime_exp (#t:limb_t) (len:BN.meta_len t) : exp t =
  match t with
  | U32 -> mk_runtime_exp_u32 len
  | U64 -> mk_runtime_exp_u64 len

let mk_runtime_exp_len_lemma #t len =
  BM.mk_runtime_mont_len_lemma #t len
