module Hacl.Bignum.Exponentiation

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery

open Hacl.Bignum.Definitions

module ST = FStar.HyperStack.ST
module S = Hacl.Spec.Bignum.Exponentiation
module LSeq = Lib.Sequence
module Loops = Lib.LoopCombinators

include Hacl.Bignum.ExpBM
include Hacl.Bignum.ExpFW

friend Hacl.Spec.Bignum.Exponentiation

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let bn_mod_exp_raw #t k bn_mod_exp_raw_precompr2 nBits n a bBits b res =
  [@inline_let] let len = k.BM.bn.BN.len in
  push_frame ();
  let r2 = create len (uint #t #SEC 0) in
  BM.precomp nBits n r2;
  bn_mod_exp_raw_precompr2 n a bBits b r2 res;
  pop_frame ()


let bn_mod_exp_ct #t k bn_mod_exp_ct_precompr2 nBits n a bBits b res =
  [@inline_let] let len = k.BM.bn.BN.len in
  push_frame ();
  let r2 = create len (uint #t #SEC 0) in
  BM.precomp nBits n r2;
  bn_mod_exp_ct_precompr2 n a bBits b r2 res;
  pop_frame ()


let bn_mod_exp_fw_raw #t k bn_mod_exp_fw_raw_precompr2 nBits n a bBits b l res =
  [@inline_let] let len = k.BM.bn.BN.len in
  push_frame ();
  let r2 = create len (uint #t #SEC 0) in
  BM.precomp nBits n r2;
  bn_mod_exp_fw_raw_precompr2 n a bBits b l r2 res;
  pop_frame ()


let bn_mod_exp_fw_ct #t k bn_mod_exp_fw_ct_precompr2 nBits n a bBits b l res =
  [@inline_let] let len = k.BM.bn.BN.len in
  push_frame ();
  let r2 = create len (uint #t #SEC 0) in
  BM.precomp nBits n r2;
  bn_mod_exp_fw_ct_precompr2 n a bBits b l r2 res;
  pop_frame ()


/// A fully runtime implementation of modular exponentiation.

[@CInline]
let bn_check_mod_exp_u32 (len:BN.meta_len U32) : bn_check_mod_exp_st U32 len =
  bn_check_mod_exp (BM.mk_runtime_mont len)
[@CInline]
let bn_mod_exp_raw_precompr2_u32 (len:BN.meta_len U32) : bn_mod_exp_raw_precompr2_st U32 len =
  bn_mod_exp_raw_precompr2 (BM.mk_runtime_mont len)
[@CInline]
let bn_mod_exp_ct_precompr2_u32 (len:BN.meta_len U32) : bn_mod_exp_ct_precompr2_st U32 len =
  bn_mod_exp_ct_precompr2 (BM.mk_runtime_mont len)
[@CInline]
let bn_mod_exp_fw_raw_precompr2_u32 (len:BN.meta_len U32) : bn_mod_exp_fw_precompr2_st U32 len =
  bn_mod_exp_fw_raw_precompr2 (BM.mk_runtime_mont len)
[@CInline]
let bn_mod_exp_fw_ct_precompr2_u32 (len:BN.meta_len U32) : bn_mod_exp_fw_precompr2_st U32 len =
  bn_mod_exp_fw_ct_precompr2 (BM.mk_runtime_mont len)

inline_for_extraction noextract
let mk_runtime_exp_u32 (len:BN.meta_len U32) : exp U32 = {
  mont = BM.mk_runtime_mont len;
  exp_check = bn_check_mod_exp_u32 len;
  raw_mod_exp_precomp = bn_mod_exp_raw_precompr2_u32 len;
  ct_mod_exp_precomp = bn_mod_exp_ct_precompr2_u32 len;
  raw_mod_exp_fw_precomp = bn_mod_exp_fw_raw_precompr2_u32 len;
  ct_mod_exp_fw_precomp = bn_mod_exp_fw_ct_precompr2_u32 len;
  }


[@CInline]
let bn_check_mod_exp_u64 (len:BN.meta_len U64) : bn_check_mod_exp_st U64 len =
  bn_check_mod_exp (BM.mk_runtime_mont len)
[@CInline]
let bn_mod_exp_raw_precompr2_u64 (len:BN.meta_len U64) : bn_mod_exp_raw_precompr2_st U64 len =
  bn_mod_exp_raw_precompr2 (BM.mk_runtime_mont len)
[@CInline]
let bn_mod_exp_ct_precompr2_u64 (len:BN.meta_len U64) : bn_mod_exp_ct_precompr2_st U64 len =
  bn_mod_exp_ct_precompr2 (BM.mk_runtime_mont len)
[@CInline]
let bn_mod_exp_fw_raw_precompr2_u64 (len:BN.meta_len U64) : bn_mod_exp_fw_precompr2_st U64 len =
  bn_mod_exp_fw_raw_precompr2 (BM.mk_runtime_mont len)
[@CInline]
let bn_mod_exp_fw_ct_precompr2_u64 (len:BN.meta_len U64) : bn_mod_exp_fw_precompr2_st U64 len =
  bn_mod_exp_fw_ct_precompr2 (BM.mk_runtime_mont len)

inline_for_extraction noextract
let mk_runtime_exp_u64 (len:BN.meta_len U64) : exp U64 = {
  mont = BM.mk_runtime_mont len;
  exp_check = bn_check_mod_exp_u64 len;
  raw_mod_exp_precomp = bn_mod_exp_raw_precompr2_u64 len;
  ct_mod_exp_precomp = bn_mod_exp_ct_precompr2_u64 len;
  raw_mod_exp_fw_precomp = bn_mod_exp_fw_raw_precompr2_u64 len;
  ct_mod_exp_fw_precomp = bn_mod_exp_fw_ct_precompr2_u64 len;
  }


let mk_runtime_exp (#t:limb_t) (len:BN.meta_len t) : exp t =
  match t with
  | U32 -> mk_runtime_exp_u32 len
  | U64 -> mk_runtime_exp_u64 len

let mk_runtime_exp_len_lemma #t len =
  BM.mk_runtime_mont_len_lemma #t len
