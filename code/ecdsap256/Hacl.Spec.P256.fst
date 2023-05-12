module Hacl.Spec.P256

open FStar.Mul

module EC = Spec.ECC
module EP = Spec.ECC.Projective

include Spec.P256

let fadd a b = EC.fadd p256 a b
let fsub a b = EC.fsub p256 a b
let fmul a b = EC.fmul p256 a b
let finv a = EC.finv p256 a
let fsqrt a = EC.fsqrt p256 a

let qelem = x:nat{x < order}
let qadd a b = EC.qadd p256 a b
let qmul a b = EC.qmul p256 a b
let qinv a = EC.qinv p256 a

let aff_point_c = EC.aff_point_c p256
let aff_point_inv = EC.aff_point_inv p256

let proj_point = EP.proj_point p256
let proj_point_c = EP.proj_point_c p256
let point_inv = EP.point_inv p256

let point_at_inf : proj_point_c = EP.point_at_inf_c p256 ()
let is_point_at_inf = EP.is_point_at_inf p256
let g_proj : proj_point_c = EP.to_proj_point_c p256 base_point

let to_proj_point = EP.to_proj_point_c p256
let to_aff_point = EP.to_aff_point p256

let is_on_curve = EC.is_on_curve p256

let aff_point_store = EC.aff_point_store p256
let point_store (p:proj_point_c) = EC.point_store p256_concrete_ops p
let aff_point_load = EC.aff_point_load p256
let load_point = EC.load_point p256_concrete_ops
let aff_point_decompress = EC.aff_point_decompress p256
let recover_y = EC.recover_y p256

let point_add = EP.point_add_a3 p256
let point_double = EP.point_double_a3 p256
let point_mul = EP.point_mul p256
let point_mul_g = Spec.ECC.point_mul_g p256_concrete_ops
let point_mul_double_g = EP.point_mul_double_g p256

let ecdsa_sign_msg_as_qelem = EC.ecdsa_sign_msg_as_qelem p256_concrete_ops
let ecdsa_verify_msg_as_qelem = Spec.ECC.ecdsa_verify_msg_as_qelem p256_concrete_ops
