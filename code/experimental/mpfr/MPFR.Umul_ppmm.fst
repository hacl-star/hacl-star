module MPFR.Umul_ppmm

open FStar.UInt64

module U128 = FStar.UInt128

type u64 = FStar.UInt64.t

val umul_ppmm: m:u64 -> n:u64 ->
    Tot (r:(u64 * u64){let a, b = r in op_Multiply (v a) (pow2 64) + v b = op_Multiply (v m) (v n)})

let umul_ppmm m n =
    let p = U128.mul_wide m n in
    U128.(uint128_to_uint64 (shift_right p 64ul)), U128.uint128_to_uint64 p
