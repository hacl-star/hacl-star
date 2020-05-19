module Hacl.HPKE.Curve51_CP128_SHA512

open Hacl.Meta.HPKE

module IDH = Hacl.HPKE.Interface.DH
module IHK = Hacl.HPKE.Interface.HKDF
module IHash = Hacl.HPKE.Interface.Hash
module IAEAD = Hacl.HPKE.Interface.AEAD

friend Hacl.Meta.HPKE

#set-options "--fuel 0 --ifuel 0"

let setupBaseI = hpke_setupBaseI_higher #cs True IHK.hkdf_expand512 IHK.hkdf_extract512 IHash.hash_sha512 IDH.secret_to_public_c51 IDH.dh_c51

let setupBaseR = hpke_setupBaseR_higher #cs True IHK.hkdf_expand512 IHK.hkdf_extract512 IHash.hash_sha512 IDH.dh_c51 IDH.secret_to_public_c51

let sealBase = hpke_sealBase_higher #cs True setupBaseI IAEAD.aead_encrypt_cp128

let openBase = hpke_openBase_higher #cs True setupBaseR IAEAD.aead_decrypt_cp128
