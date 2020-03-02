module Hacl.Impl.Curve25519.Field64.Vale

open Hacl.Impl.Curve25519.Fields.Core

val add_scalar: add1_t
val fadd: fadd_t M64
val fsub: fsub_t M64
val fmul: fmul_t M64
val fmul2: fmul2_t M64
val fmul_scalar: fmul1_t M64
val fsqr: fsqr_t M64
val fsqr2: fsqr2_t M64
val cswap2: cswap2_t M64
