module Hacl.HPKE.Curve51_CP256_SHA512

open Hacl.Meta.HPKE

module IDH = Hacl.Impl.Generic.DH
module IHK = Hacl.Impl.Generic.HKDF
module IHash = Hacl.Impl.Generic.Hash
module IAEAD = Hacl.Impl.Instantiate.AEAD

friend Hacl.Meta.HPKE

let setupBaseI = hpke_setupBaseI_higher #cs IHK.hkdf_expand512 IHK.hkdf_extract512 IHash.hash_sha512 IDH.secret_to_public_c51 IDH.scalarmult_c51

let setupBaseR = hpke_setupBaseR_higher #cs IHK.hkdf_expand512 IHK.hkdf_extract512 IHash.hash_sha512 IDH.scalarmult_c51 IDH.secret_to_public_c51

let sealBase = hpke_sealBase_higher #cs setupBaseI IAEAD.aead_encrypt_cp256

let openBase = hpke_openBase_higher #cs setupBaseR IAEAD.aead_decrypt_cp256
