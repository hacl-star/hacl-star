module Hacl.HPKE.Curve51_CP256_SHA256

open Hacl.Meta.HPKE

module IDH = Hacl.HPKE.Interface.DH
module IHK = Hacl.HPKE.Interface.HKDF
module IHash = Hacl.HPKE.Interface.Hash
module IAEAD = Hacl.HPKE.Interface.AEAD

friend Hacl.Meta.HPKE

#set-options "--fuel 0 --ifuel 0"

let setupBaseS = hpke_setupBaseS_higher #cs True IDH.secret_to_public_c51 IDH.dh_c51

let setupBaseR = hpke_setupBaseR_higher #cs True IDH.dh_c51 IDH.secret_to_public_c51

let sealBase = hpke_sealBase_higher #cs True IAEAD.aead_encrypt_cp256 setupBaseS

let openBase = hpke_openBase_higher #cs True IAEAD.aead_decrypt_cp256 setupBaseR
