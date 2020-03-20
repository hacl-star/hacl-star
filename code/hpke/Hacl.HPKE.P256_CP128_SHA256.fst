module Hacl.HPKE.P256_CP128_SHA256

open Hacl.Meta.HPKE

module IDH = Hacl.Impl.Generic.DH
module IHK = Hacl.Impl.Generic.HKDF
module IHash = Hacl.Impl.Generic.Hash
module IAEAD = Hacl.Impl.Instantiate.AEAD

friend Hacl.Meta.HPKE

#set-options "--fuel 0 --ifuel 0"

let setupBaseI = hpke_setupBaseI_higher #cs True IHK.hkdf_expand256 IHK.hkdf_extract256 IHash.hash_sha256 IDH.secret_to_public_p256 IDH.dh_p256

let setupBaseR = hpke_setupBaseR_higher #cs True IHK.hkdf_expand256 IHK.hkdf_extract256 IHash.hash_sha256 IDH.dh_p256 IDH.secret_to_public_p256

let sealBase = hpke_sealBase_higher #cs True setupBaseI IAEAD.aead_encrypt_cp128

let openBase = hpke_openBase_higher #cs True setupBaseR IAEAD.aead_decrypt_cp128
