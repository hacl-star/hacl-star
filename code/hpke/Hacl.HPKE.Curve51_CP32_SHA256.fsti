module Hacl.HPKE.Curve51_CP32_SHA256

open Hacl.Impl.HPKE
module S = Spec.Agile.HPKE
module DH = Spec.Agile.DH
module AEAD = Spec.Agile.AEAD
module Hash = Spec.Agile.Hash

noextract unfold
let cs:S.ciphersuite = (DH.DH_Curve25519, Hash.SHA2_256, S.Seal AEAD.CHACHA20_POLY1305, Hash.SHA2_256)

val setupBaseS: setupBaseS_st cs True

val setupBaseR: setupBaseR_st cs True

val sealBase: sealBase_st cs True

val openBase: openBase_st cs True
