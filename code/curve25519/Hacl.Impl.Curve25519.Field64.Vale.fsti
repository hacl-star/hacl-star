module Hacl.Impl.Curve25519.Field64.Vale

open Hacl.Impl.Curve25519.Fields.Core

// Note: this doesn't work and the types don't reduce.
// inline_for_extraction
// let i: index = M64, Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)

val add_scalar: add1_t (M64, Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled))
val fadd: fadd_t (M64, Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled))
val fsub: fsub_t (M64, Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled))
val fmul: fmul_t (M64, Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled))
val fmul2: fmul2_t (M64, Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled))
val fmul_scalar: fmul1_t (M64, Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled))
val fsqr: fsqr_t (M64, Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled))
val fsqr2: fsqr2_t (M64, Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled))
val cswap2: cswap2_t (M64, Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled))
