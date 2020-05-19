module Hacl.Curve25519_64_Slow

friend Hacl.Meta.Curve25519
open Hacl.Meta.Curve25519

// The Vale core.
module C = Hacl.Impl.Curve25519.Field64.Hacl

let g25519: g25519_t =
  Lib.Buffer.createL_global Spec.Curve25519.basepoint_list

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"
let point_add_and_double =
  addanddouble_point_add_and_double_higher #M64 True C.fmul_ C.fsqr2_ C.fmul1_ C.fmul2_ C.fsub_ C.fadd_
let point_double =
  addanddouble_point_double_higher #M64 True C.fmul2_ C.fmul1_ C.fsqr2_ C.fsub_ C.fadd_
let montgomery_ladder =
  generic_montgomery_ladder_higher #M64 True point_double C.cswap2_ point_add_and_double
let fsquare_times = finv_fsquare_times_higher #M64 True C.fsqr_
let finv = finv_finv_higher #M64 True fsquare_times C.fmul_
// Note that here, for implementations of Curve64, we have a generic store_felem
// over an *implementation* of add1. (For Curve51, store_felem does not have
// that generic aspect.)
let store_felem = fields_store_felem_higher #M64 True C.add1_
let encode_point = generic_encode_point_higher #M64 True store_felem C.fmul_ finv
let scalarmult = generic_scalarmult_higher #M64 True encode_point montgomery_ladder decode_point
let secret_to_public = generic_secret_to_public_higher #M64 True scalarmult g25519
let ecdh = generic_ecdh_higher #M64 True scalarmult

