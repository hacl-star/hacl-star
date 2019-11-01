module Hacl.HPKE.Curve51_CP32_SHA256

open Hacl.Meta.HPKE

module IDH = Hacl.Impl.Generic.DH
module IHK = Hacl.Impl.Generic.HKDF
module IAEAD = Hacl.Impl.Instantiate.AEAD

friend Hacl.Meta.HPKE

let setupBaseI = hpke_setupBaseI_higher #cs IHK.hkdf_expand256 IHK.hkdf_extract256 IDH.secret_to_public_c51 IDH.scalarmult_c51

let setupBaseR = hpke_setupBaseR_higher #cs IHK.hkdf_expand256 IHK.hkdf_extract256 IDH.scalarmult_c51 IDH.secret_to_public_c51

let encryptBase = hpke_encryptBase_higher #cs IDH.scalarmult_c51 IDH.secret_to_public_c51
  setupBaseI IAEAD.aead_encrypt_cp32

let decryptBase = hpke_decryptBase_higher #cs IDH.scalarmult_c51 setupBaseR IAEAD.aead_decrypt_cp32
