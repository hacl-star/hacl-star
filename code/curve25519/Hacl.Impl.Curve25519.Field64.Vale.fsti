module Hacl.Impl.Curve25519.Field64.Vale

open Hacl.Impl.Curve25519.Fields.Core

let p = Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)

val add_scalar: add1_t p
val fadd: fadd_t M64 p
val fsub: fsub_t M64 p
val fmul: fmul_t M64 p
val fmul2: fmul2_t M64 p
val fmul_scalar: fmul1_t M64 p
val fsqr: fsqr_t M64 p
val fsqr2: fsqr2_t M64 p
val cswap2: cswap2_t M64 p
