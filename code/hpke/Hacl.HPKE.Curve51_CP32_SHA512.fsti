module Hacl.HPKE.Curve51_CP32_SHA512

open Hacl.Impl.HPKE
module DH = Spec.Agile.DH
module AEAD = Spec.Agile.AEAD
module Hash = Spec.Agile.Hash

noextract unfold
let cs = (DH.DH_Curve25519, AEAD.CHACHA20_POLY1305, Hash.SHA2_512)

val setupBaseI: setupBaseI_st cs

val setupBaseR: setupBaseR_st cs

val sealBase: sealBase_st cs

val openBase: openBase_st cs
