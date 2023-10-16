module Hacl.Impl.PCurves.Bignum.P521

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

module S = Spec.PCurves
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence
module BD = Hacl.Spec.Bignum.Definitions

module BM = Hacl.Bignum.Montgomery
module SM = Hacl.Spec.Bignum.Montgomery

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

module BN = Hacl.Bignum
open Spec.P521
open Hacl.Impl.PCurves.Bignum

[@CInline]
val bn_is_eq_mask: bn_is_eq_mask_t
let bn_is_eq_mask x y = (bn_is_eq_mask_g x y)

[@CInline]
val bn_cmovznz: bn_cmovznz_t
let bn_cmovznz a b c d = (bn_cmovznz_g a b c d)

[@CInline]
val bn_add_mod: bn_add_mod_t
let bn_add_mod a b c d = (bn_add_mod_g a b c d)

[@CInline]
val bn_sub: bn_sub_t
let bn_sub a b c = (bn_sub_g a b c)

[@CInline]
val bn_sub_mod: bn_sub_mod_t
let bn_sub_mod a b c d = (bn_sub_mod_g a b c d)

[@CInline]
val bn_mul: bn_mul_t
let bn_mul a b c = (bn_mul_g a b c)

[@CInline]
val bn_sqr: bn_sqr_t
let bn_sqr a b = (bn_sqr_g a b)

[@CInline]
val bn_to_bytes_be: bn_to_bytes_be_t
let bn_to_bytes_be a b =  (bn_to_bytes_be_g a b)

[@CInline]
val bn_from_bytes_be: bn_from_bytes_be_t
let bn_from_bytes_be a b =  (bn_from_bytes_be_g a b)

inline_for_extraction noextract
val bn_mont_reduction: bn_mont_reduction_t
let bn_mont_reduction a b c d =  (bn_mont_reduction_g a b c d)

inline_for_extraction noextract
instance p521_bn_ops : bn_ops = {
  bn_is_eq_mask;
  bn_cmovznz;
  bn_add_mod;
  bn_sub;
  bn_sub_mod;
  bn_mul;
  bn_sqr;
  bn_to_bytes_be;
  bn_from_bytes_be;
  bn_mont_reduction
}
