module Hacl.Curve25519_51

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Curve25519.Fields
open Hacl.Impl.Curve25519.Generic

module S = Spec.Curve25519

friend Hacl.Meta.Curve25519

open Hacl.Meta.Curve25519

// The Vale core.
module C = Hacl.Impl.Curve25519.Field51.Core

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"
let decode_point = Hacl.Impl.Curve25519.Generic.decode_point #M51
let cswap2 = generic_cswap2_higher #M51 C.cswap2
let fadd = fields_fadd_higher #M51 C.fadd
let fsub = fields_fsub_higher #M51 C.fsub
let fmul2 = fields_fmul2_higher #M51 C.fmul2
let point_add_and_double0 = addanddouble_point_add_and_double0_higher #M51 fmul2 fsub fadd
let fsqr2 = fields_fsqr2_higher #M51 C.fsqr2
let fmul1 = fields_fmul1_higher #M51 C.fmul1
let point_add_and_double1 =
  addanddouble_point_add_and_double1_higher #M51 C.fmul2 C.fadd C.fmul1 C.fsub C.fsqr2
let fmul = fields_fmul_higher #M51 C.fmul
let point_add_and_double =
  addanddouble_point_add_and_double_higher #M51 C.fmul C.fsqr2 C.fmul1 C.fmul2 C.fsub C.fadd
let ladder_step = generic_ladder_step_higher #M51 point_add_and_double C.cswap2
let ladder_step_loop = generic_ladder_step_loop_higher #M51 C.cswap2 point_add_and_double
let ladder0_ = generic_ladder0__higher #M51 point_add_and_double C.cswap2
let point_double_higher =
  addanddouble_point_double_higher #M51 C.fmul2 C.fmul1 C.fsqr2 C.fsub C.fadd
let ladder1__higher = generic_ladder1__higher #M51 point_double
let ladder2__higher = generic_ladder2__higher #M51 point_double C.cswap2 point_add_and_double
let ladder4__higher = generic_ladder4__higher #M51 point_add_and_double C.cswap2 point_double
let montgomery_ladder_higher =
  generic_montgomery_ladder_higher #M51 point_double C.cswap2 point_add_and_double
let fsqr_s_higher = finv_fsqr_s_higher #M51 C.fsqr
let fsquare_times_higher = finv_fsquare_times_higher #M51 C.fsqr
let fmul_s_higher = finv_fmul_s_higher #M51 C.fmul
let finv0_higher = finv_finv0_higher #M51 C.fmul fsquare_times
let finv_higher = finv_finv_higher #M51 fsquare_times C.fmul
let carry_pass_store_higher = field51_carry_pass_store_higher C.add1
let store_felem_higher = field51_store_felem_higher C.add1
let store_felem_higher' = fields_store_felem_higher #M51 C.add1
let encode_point_higher = generic_encode_point_higher #M51 C.add1 C.fmul finv
let scalarmult_higher = generic_scalarmult_higher #M51 encode_point montgomery_ladder decode_point
let secret_to_public_higher = generic_secret_to_public_higher #M51 scalarmult
let ecdh_higher = generic_ecdh_higher #M51 scalarmult

