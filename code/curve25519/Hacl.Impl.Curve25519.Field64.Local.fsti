module Hacl.Impl.Curve25519.Field64.Local

open Hacl.Impl.Curve25519.Fields.Core

/// This version is only assumed. We can't play tricks with include directories
/// and removing the fst from the include path because this leaves invalid build
/// artifacts in the shared obj directory.

val add1: add1_t True
val fadd: fadd_t M64 True
val fsub: fsub_t M64 True
val fmul: fmul_t M64 True
val fmul2: fmul2_t M64 True
val fmul1: fmul1_t M64 True
val fsqr: fsqr_t M64 True
val fsqr2: fsqr2_t M64 True
val cswap2: cswap2_t M64 True
