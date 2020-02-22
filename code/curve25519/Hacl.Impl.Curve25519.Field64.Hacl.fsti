module Hacl.Impl.Curve25519.Field64.Hacl

open Hacl.Impl.Curve25519.Fields.Core

// Note: this doesn't work and the types don't reduce.
// inline_for_extraction
// let i: index = M64, True

val add1_: add1_t (M64, True)
val fadd_: fadd_t (M64, True)
val fsub_: fsub_t (M64, True)
val fmul_: fmul_t (M64, True)
val fmul2_: fmul2_t (M64, True)
val fmul1_: fmul1_t (M64, True)
val fsqr_: fsqr_t (M64, True)
val fsqr2_: fsqr2_t (M64, True)
val cswap2_: cswap2_t (M64, True)
