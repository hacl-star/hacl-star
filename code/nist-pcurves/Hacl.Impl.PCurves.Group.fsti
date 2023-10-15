module Hacl.Impl.PCurves.Group

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

module BE = Hacl.Impl.Exponentiation.Definitions

module S = Spec.PCurves
module SL = Spec.PCurves.Lemmas

open Hacl.Impl.PCurves.Bignum
open Hacl.Impl.PCurves.Field
open Hacl.Impl.PCurves.Constants
open Hacl.Impl.PCurves.InvSqrt
open Hacl.Impl.PCurves.Point

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

unfold
let linv_ctx (a:LSeq.lseq uint64 0) : Type0 = True

unfold
let refl {| cp:S.curve_params |} (p:LSeq.lseq uint64 (3*v cp.bn_limbs){point_inv_seq p}) : GTot S.aff_point =
  S.to_aff_point (from_mont_point (as_point_nat_seq p))

[@(strict_on_arguments [0])]
inline_for_extraction noextract
let mk_to_pcurve_comm_monoid {| cp:S.curve_params |} : BE.to_comm_monoid U64 (3ul *. cp.bn_limbs) 0ul = {
  BE.a_spec = S.aff_point;
  BE.comm_monoid = S.mk_pcurve_comm_monoid;
  BE.linv_ctx = linv_ctx;
  BE.linv = point_inv_seq;
  BE.refl = refl;
}


inline_for_extraction noextract
let point_add_t {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt|} = BE.lmul_st U64 (3ul *. cp.bn_limbs) 0ul mk_to_pcurve_comm_monoid

[@(strict_on_arguments [0;1;2;3;4])]
inline_for_extraction noextract
val point_add_g {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt|} : point_add_t

inline_for_extraction noextract
let point_double_t {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt|} = BE.lsqr_st U64 (3ul *. cp.bn_limbs) 0ul mk_to_pcurve_comm_monoid

[@(strict_on_arguments [0;1;2;3;4])]
inline_for_extraction noextract
val point_double_g {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt|}: point_double_t

inline_for_extraction noextract
let point_zero_t {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt|} = BE.lone_st U64 (3ul *. cp.bn_limbs) 0ul mk_to_pcurve_comm_monoid

[@(strict_on_arguments [0;1;2;3;4])]
inline_for_extraction noextract
val point_zero_g {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt|} : point_zero_t

[@(strict_on_arguments [0;1;2;3;4])]
inline_for_extraction
class point_ops {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| field_ops |} {| curve_inv_sqrt|} = {
  point_add: point_add_t;
  point_double: point_double_t;
  point_zero: point_zero_t;
}

[@(strict_on_arguments [0;1;2;3;4;5])]
inline_for_extraction noextract
let mk_pcurve_concrete_ops {| S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt|} {| p:point_ops |} : BE.concrete_ops U64 (3ul *. S.bn_limbs) 0ul = {
  BE.to = mk_to_pcurve_comm_monoid;
  BE.lone = p.point_zero;
  BE.lmul = p.point_add;
  BE.lsqr = p.point_double;
}


