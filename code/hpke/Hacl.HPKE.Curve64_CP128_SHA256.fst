module Hacl.HPKE.Curve64_CP128_SHA256

open Hacl.Meta.HPKE

module IDH = Hacl.HPKE.Interface.DH
module IHK = Hacl.HPKE.Interface.HKDF
module IAEAD = Hacl.HPKE.Interface.AEAD

friend Hacl.Meta.HPKE

#set-options "--fuel 0 --ifuel 0"

let setupBaseS = hpke_setupBaseS_higher #cs vale_p IHK.hkdf_expand256 IHK.hkdf_extract256 IDH.secret_to_public_c64 IDH.dh_c64 IHK.hkdf_expand256 IHK.hkdf_extract256

let setupBaseR = hpke_setupBaseR_higher #cs vale_p IHK.hkdf_expand256 IHK.hkdf_extract256 IDH.dh_c64 IHK.hkdf_expand256 IHK.hkdf_extract256 IDH.secret_to_public_c64

let sealBase = hpke_sealBase_higher #cs vale_p IAEAD.aead_encrypt_cp128 setupBaseS

let openBase = hpke_openBase_higher #cs vale_p IAEAD.aead_decrypt_cp128 setupBaseR
