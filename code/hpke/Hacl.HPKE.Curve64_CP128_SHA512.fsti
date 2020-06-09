module Hacl.HPKE.Curve64_CP128_SHA512

open Hacl.Impl.HPKE
module DH = Spec.Agile.DH
module AEAD = Spec.Agile.AEAD
module Hash = Spec.Agile.Hash

noextract unfold
let cs = (DH.DH_Curve25519, AEAD.CHACHA20_POLY1305, Hash.SHA2_512)

noextract unfold
let vale_p = Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)

val setupBaseS: setupBaseS_st cs vale_p

val setupBaseR: setupBaseR_st cs vale_p

val sealBase: sealBase_st cs vale_p

val openBase: openBase_st cs vale_p
