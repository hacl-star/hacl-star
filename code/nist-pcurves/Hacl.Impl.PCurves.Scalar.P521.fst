module Hacl.Impl.PCurves.Scalar.P521

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.PCurves.Constants
open Hacl.Impl.PCurves.Bignum

module S = Spec.PCurves
module SM = Hacl.Spec.PCurves.Montgomery
module BSeq = Lib.ByteSequence
module CC = Hacl.Impl.PCurves.Constants

open Spec.P521
open Hacl.Impl.PCurves.Bignum.P521
open Hacl.Impl.PCurves.Constants.P521
open Hacl.Impl.PCurves.Scalar

[@CInline]
val bn_is_lt_order_mask: bn_is_lt_order_mask_t
let bn_is_lt_order_mask a = bn_is_lt_order_mask_g a

[@CInline]
val load_qelem_conditional: load_qelem_conditional_t
let load_qelem_conditional a b = load_qelem_conditional_g a b

[@CInline]
val qmod_short: qmod_short_t
let qmod_short a b = qmod_short_g a b

[@CInline]
val qadd: qadd_t
let qadd a b c = qadd_g a b c

[@CInline]
val qmul: qmul_t
let qmul a b c = qmul_g a b c

[@CInline]
val qsqr: qsqr_t
let qsqr a b = qsqr_g a b

[@CInline]
val from_qmont: from_qmont_t
let from_qmont a b = from_qmont_g a b
  
[@CInline]
val to_qmont: to_qmont_t
let to_qmont a b = to_qmont_g a b
  

inline_for_extraction
instance p521_order_ops : order_ops = {
  bn_is_lt_order_mask;
  load_qelem_conditional;
  qmod_short;
  qadd;
  qmul;
  qsqr;
  from_qmont;
  to_qmont
}
