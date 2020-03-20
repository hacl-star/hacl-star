module Hacl.HPKE.P256_CP32_SHA256

open Hacl.Meta.HPKE

module IDH = Hacl.HPKE.Interface.DH
module IHK = Hacl.HPKE.Interface.HKDF
module IHash = Hacl.HPKE.Interface.Hash
module IAEAD = Hacl.HPKE.Interface.AEAD

friend Hacl.Meta.HPKE

#set-options "--fuel 0 --ifuel 0"

let setupBaseI = hpke_setupBaseI_higher #cs True IHK.hkdf_expand256 IHK.hkdf_extract256 IHash.hash_sha256 IDH.secret_to_public_p256 IDH.dh_p256

let setupBaseR = hpke_setupBaseR_higher #cs True IHK.hkdf_expand256 IHK.hkdf_extract256 IHash.hash_sha256 IDH.dh_p256 IDH.secret_to_public_p256

let sealBase = hpke_sealBase_higher #cs True setupBaseI IAEAD.aead_encrypt_cp32

let openBase = hpke_openBase_higher #cs True setupBaseR IAEAD.aead_decrypt_cp32
