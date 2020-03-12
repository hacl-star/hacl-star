module Hacl.Impl.Curve25519.Field64.Hacl

open Hacl.Impl.Curve25519.Fields.Core

val add1_: add1_t True
val fadd_: fadd_t M64 True
val fsub_: fsub_t M64 True
val fmul_: fmul_t M64 True
val fmul2_: fmul2_t M64 True
val fmul1_: fmul1_t M64 True
val fsqr_: fsqr_t M64 True
val fsqr2_: fsqr2_t M64 True
val cswap2_: cswap2_t M64 True
