module Hacl.Bignum.AlmostMontgomery

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions
open Hacl.Bignum.Base
open Hacl.Impl.Lib

module ST = FStar.HyperStack.ST
module Loops = Lib.LoopCombinators
module LSeq = Lib.Sequence
module B = LowStar.Buffer

module S = Hacl.Spec.Bignum.AlmostMontgomery
module SB = Hacl.Spec.Bignum
module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery

friend Hacl.Spec.Bignum.AlmostMontgomery
friend Hacl.Bignum.Montgomery

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let bn_almost_mont_reduction #t k n nInv c res =
  [@inline_let] let len = k.BN.len in
  push_frame ();
  let c0 = BM.bn_mont_reduction_loop_div_r #t k n nInv c res in
  let tmp = create len (uint #t #SEC 0) in
  let c1 = k.BN.sub res n tmp in
  map2T len res (mask_select (uint #t 0 -. c0)) tmp res;
  pop_frame ()


let bn_almost_mont_mul #t k almost_mont_reduction n nInv_u64 aM bM resM =
  [@inline_let] let len = k.BN.len in
  push_frame ();
  let c = create (len +! len) (uint #t 0) in
  k.BN.mul aM bM c;
  almost_mont_reduction n nInv_u64 c resM;
  pop_frame ()


let bn_almost_mont_sqr #t k almost_mont_reduction n nInv_u64 aM resM =
  [@inline_let] let len = k.BN.len in
  push_frame ();
  let c = create (len +! len) (uint #t 0) in
  k.BN.sqr aM c;
  almost_mont_reduction n nInv_u64 c resM;
  pop_frame ()


let bn_almost_mont_reduction_u32 (len:BN.meta_len U32) : bn_almost_mont_reduction_st U32 len =
  bn_almost_mont_reduction (BN.mk_runtime_bn U32 len)
let bn_almost_mont_mul_u32 (len:BN.meta_len U32) : bn_almost_mont_mul_st U32 len =
  bn_almost_mont_mul (BN.mk_runtime_bn U32 len) (bn_almost_mont_reduction_u32 len)
let bn_almost_mont_sqr_u32 (len:BN.meta_len U32) : bn_almost_mont_sqr_st U32 len =
  bn_almost_mont_sqr (BN.mk_runtime_bn U32 len) (bn_almost_mont_reduction_u32 len)

inline_for_extraction noextract
let mk_runtime_almost_mont_u32 (len:BN.meta_len U32) : almost_mont U32 = {
  bn = BN.mk_runtime_bn U32 len;
  mont_check = BM.bn_check_modulus_u32 len;
  precomp = BM.bn_precomp_r2_mod_n_u32 len;
  reduction = bn_almost_mont_reduction_u32 len;
  to = BM.bn_to_mont_u32 len;
  from = BM.bn_from_mont_u32 len;
  mul = bn_almost_mont_mul_u32 len;
  sqr = bn_almost_mont_sqr_u32 len;
}


let bn_almost_mont_reduction_u64 (len:BN.meta_len U64) : bn_almost_mont_reduction_st U64 len =
  bn_almost_mont_reduction (BN.mk_runtime_bn U64 len)
let bn_almost_mont_mul_u64 (len:BN.meta_len U64) : bn_almost_mont_mul_st U64 len =
  bn_almost_mont_mul (BN.mk_runtime_bn U64 len) (bn_almost_mont_reduction_u64 len)
let bn_almost_mont_sqr_u64 (len:BN.meta_len U64) : bn_almost_mont_sqr_st U64 len =
  bn_almost_mont_sqr (BN.mk_runtime_bn U64 len) (bn_almost_mont_reduction_u64 len)

inline_for_extraction noextract
let mk_runtime_almost_mont_u64 (len:BN.meta_len U64) : almost_mont U64 = {
  bn = BN.mk_runtime_bn U64 len;
  mont_check = BM.bn_check_modulus_u64 len;
  precomp = BM.bn_precomp_r2_mod_n_u64 len;
  reduction = bn_almost_mont_reduction_u64 len;
  to = BM.bn_to_mont_u64 len;
  from = BM.bn_from_mont_u64 len;
  mul = bn_almost_mont_mul_u64 len;
  sqr = bn_almost_mont_sqr_u64 len;
}


let mk_runtime_almost_mont (#t:limb_t) (len:BN.meta_len t) : almost_mont t =
  match t with
  | U32 -> mk_runtime_almost_mont_u32 len
  | U64 -> mk_runtime_almost_mont_u64 len

let mk_runtime_almost_mont_len_lemma #t len = ()
