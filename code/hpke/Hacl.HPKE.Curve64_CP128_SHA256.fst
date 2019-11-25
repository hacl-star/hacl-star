module Hacl.HPKE.Curve64_CP128_SHA256

open Hacl.Meta.HPKE

module IDH = Hacl.Impl.Generic.DH
module IHK = Hacl.Impl.Generic.HKDF
module IHash = Hacl.Impl.Generic.Hash
module IAEAD = Hacl.Impl.Instantiate.AEAD

friend Hacl.Meta.HPKE

let setupBaseI = hpke_setupBaseI_higher #cs IHK.hkdf_expand256 IHK.hkdf_extract256 IHash.hash_sha256 IDH.secret_to_public_c64 IDH.scalarmult_c64

let setupBaseR = hpke_setupBaseR_higher #cs IHK.hkdf_expand256 IHK.hkdf_extract256 IHash.hash_sha256 IDH.scalarmult_c64 IDH.secret_to_public_c64

let sealBase = hpke_sealBase_higher #cs setupBaseI IAEAD.aead_encrypt_cp128

let openBase = hpke_openBase_higher #cs setupBaseR IAEAD.aead_decrypt_cp128
