module Hacl.Curve25519_64

friend Hacl.Meta.Curve25519
open Hacl.Meta.Curve25519

// The Vale core.
module C = Hacl.Impl.Curve25519.Field64.Vale

let g25519: g25519_t =
  Lib.Buffer.createL_global Spec.Curve25519.basepoint_list

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"
let point_add_and_double =
  addanddouble_point_add_and_double_higher #M64 C.p C.fmul C.fsqr2 C.fmul_scalar C.fmul2 C.fsub C.fadd
let point_double =
  addanddouble_point_double_higher #M64 C.p C.fmul2 C.fmul_scalar C.fsqr2 C.fsub C.fadd
let montgomery_ladder =
  generic_montgomery_ladder_higher #M64 C.p point_double C.cswap2 point_add_and_double
let fsquare_times = finv_fsquare_times_higher #M64 C.p C.fsqr
let finv = finv_finv_higher #M64 C.p C.fmul fsquare_times
// Note that here, for implementations of Curve64, we have a generic store_felem
// over an *implementation* of add1. (For Curve51, store_felem does not have
// that generic aspect.)
let store_felem = fields_store_felem_higher #M64 C.p C.add_scalar
let encode_point = generic_encode_point_higher #M64 C.p store_felem C.fmul finv
let scalarmult = generic_scalarmult_higher #M64 C.p encode_point montgomery_ladder decode_point
let secret_to_public = generic_secret_to_public_higher #M64 C.p scalarmult g25519
let ecdh = generic_ecdh_higher #M64 C.p scalarmult
