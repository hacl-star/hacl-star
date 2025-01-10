module Hacl.Impl.PCurves.PointMul

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.PCurves.Bignum
open Hacl.Impl.PCurves.Field
open Hacl.Impl.PCurves.Constants
open Hacl.Impl.PCurves.InvSqrt
open Hacl.Impl.PCurves.Point

module S = Spec.PCurves
module BE = Hacl.Impl.Exponentiation

include Hacl.Impl.PCurves.Group
include Hacl.Impl.PCurves.PrecompTable

inline_for_extraction noextract
let table_inv_w4 {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt |} {| point_ops |}: BE.table_inv_t U64 (3ul *. cp.bn_limbs) 16ul =
  [@inline_let] let len = 3ul *. cp.bn_limbs in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_pcurve_concrete_ops in
  [@inline_let] let l = 4ul in
  [@inline_let] let table_len = 16ul in
  BE.table_inv_precomp len ctx_len k l table_len


inline_for_extraction noextract
let table_inv_w5 {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt |} {| point_ops |}: BE.table_inv_t U64 (3ul *. cp.bn_limbs) 32ul =
  [@inline_let] let len = 3ul *. cp.bn_limbs in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_pcurve_concrete_ops in
  [@inline_let] let l = 5ul in
  [@inline_let] let table_len = 32ul in
  assert_norm (pow2 (v l) == v table_len);
  BE.table_inv_precomp len ctx_len k l table_len

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"
noextract inline_for_extraction
let point_mul_t {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |}
              {| curve_inv_sqrt|} {| point_ops |} {| pt:precomp_tables |} =
  res:point -> scalar:felem -> p:point -> Stack unit
  (requires fun h ->
    live h p /\ live h res /\ live h scalar /\
    disjoint p res /\ disjoint scalar res /\ disjoint p scalar /\
    point_inv h p /\ as_nat h scalar < S.order)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    point_inv h1 res /\
    S.to_aff_point (from_mont_point (as_point_nat h1 res)) ==
    S.to_aff_point (S.point_mul (as_nat h0 scalar) (from_mont_point (as_point_nat h0 p))))

[@(strict_on_arguments [0;1;2;3;4;5;6])]
noextract inline_for_extraction
val point_mul_gen {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |}
              {| curve_inv_sqrt|} {| point_ops |} {| pt:precomp_tables |}: point_mul_t


noextract inline_for_extraction
let point_mul_g_t {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |}
                {| curve_inv_sqrt|} {| point_ops |} {| pt:precomp_tables |} =
  res:point -> scalar:felem -> Stack unit
  (requires fun h ->
    live h res /\ live h scalar /\ disjoint res scalar /\
    as_nat h scalar < S.order)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    point_inv h1 res /\
    S.to_aff_point (from_mont_point (as_point_nat h1 res)) ==
    S.to_aff_point (S.point_mul_g (as_nat h0 scalar)))

noextract inline_for_extraction
let point_mul_double_g_t {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |}
                       {| curve_inv_sqrt|} {| point_ops |} {| pt:precomp_tables |} = 
  res:point -> scalar1:felem -> scalar2:felem -> p:point -> Stack unit
  (requires fun h ->
    live h res /\ live h scalar1 /\ live h scalar2 /\ live h p /\
    disjoint res scalar1 /\ disjoint res scalar2 /\ disjoint res p /\
    disjoint p scalar1 /\ disjoint p scalar2 /\
    point_inv h p /\ as_nat h scalar1 < S.order /\ as_nat h scalar2 < S.order)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    point_inv h1 res /\
    S.to_aff_point (from_mont_point (as_point_nat h1 res)) ==
    S.to_aff_point (S.point_mul_double_g (as_nat h0 scalar1) (as_nat h0 scalar2)
      (from_mont_point (as_point_nat h0 p))))

inline_for_extraction
class point_mul_ops {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |}
                    {| curve_inv_sqrt|} {| point_ops |} {| pt:precomp_tables |} = {
      point_mul: point_mul_t;
      point_mul_g: point_mul_g_t;
      point_mul_double_g: point_mul_double_g_t
}
