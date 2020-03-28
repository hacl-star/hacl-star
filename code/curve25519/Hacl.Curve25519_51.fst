module Hacl.Curve25519_51

friend Hacl.Meta.Curve25519
open Hacl.Meta.Curve25519

// The Hacl core.
module C = Hacl.Impl.Curve25519.Field51

let g25519: g25519_t =
  Lib.Buffer.createL_global Spec.Curve25519.basepoint_list

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"
let point_add_and_double =
  addanddouble_point_add_and_double_higher #M51 True C.fmul C.fsqr2 C.fmul1 C.fmul2 C.fsub C.fadd
let point_double =
  addanddouble_point_double_higher #M51 True C.fmul2 C.fmul1 C.fsqr2 C.fsub C.fadd
let montgomery_ladder =
  generic_montgomery_ladder_higher #M51 True point_double C.cswap2 point_add_and_double
let fsquare_times = finv_fsquare_times_higher #M51 True C.fsqr
let finv = finv_finv_higher #M51 True fsquare_times C.fmul
let encode_point = generic_encode_point_higher #M51 True C.store_felem C.fmul finv
let scalarmult = generic_scalarmult_higher #M51 True encode_point montgomery_ladder decode_point
let secret_to_public = generic_secret_to_public_higher #M51 True scalarmult g25519
let ecdh = generic_ecdh_higher #M51 True scalarmult
