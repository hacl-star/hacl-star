module Hacl.Impl.PCurves.Field.P256

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer


module S = Spec.PCurves
module SM = Hacl.Spec.PCurves.Montgomery
module CC = Hacl.Impl.PCurves.Constants

open Spec.P256
open Hacl.Impl.PCurves.Constants.P256
open Hacl.Impl.PCurves.Bignum.P256
open Hacl.Impl.PCurves.Field

[@CInline]
val bn_is_lt_prime_mask: bn_is_lt_prime_mask_t
let bn_is_lt_prime_mask f = bn_is_lt_prime_mask_g f

[@CInline]
val fadd: fadd_t
let fadd a b c = fadd_g a b c

[@CInline]
val fsub: fsub_t
let fsub a b c = fsub_g a b c

[@CInline]
val fmul: fmul_t
let fmul a b c = fmul_g a b c

[@CInline]
val fsqr: fsqr_t
let fsqr a b = fsqr_g a b

[@CInline]
val from_mont: from_mont_t
let from_mont a b = from_mont_g a b

[@CInline]
val to_mont: to_mont_t
let to_mont a b = to_mont_g a b

inline_for_extraction
instance p256_field_ops: field_ops = {
  bn_is_lt_prime_mask;
  fadd;
  fsub;
  fmul;
  fsqr;
  from_mont;
  to_mont
}
