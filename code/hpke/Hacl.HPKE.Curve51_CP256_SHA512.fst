module Hacl.HPKE.Curve51_CP256_SHA512

open Hacl.Meta.HPKE

module IDH = Hacl.HPKE.Interface.DH
module IHK = Hacl.HPKE.Interface.HKDF
module IAEAD = Hacl.HPKE.Interface.AEAD

friend Hacl.Meta.HPKE

#set-options "--fuel 0 --ifuel 0"

[@@ Comment "HPKE Base mode setup for a sender.

@param o_pkE Pointer to 32 bytes where the ephemeral public key is written to.
@param o_ctx The encryption context to initialize.
@param skE Pointer to 32 bytes where the ephemeral secret key is read from.
@param pkR Pointer to 32 bytes where the recipient's public key is read from.
@param infolen Length of the info string.
@param info Pointer to `infolen` bytes of info string.

@returns 0 on success, non-zero on failure."]
let setupBaseS = hpke_setupBaseS_higher #cs True IHK.hkdf_expand512 IHK.hkdf_extract512 IDH.secret_to_public_c51 IDH.dh_c51 IHK.hkdf_expand256 IHK.hkdf_extract256

[@@ Comment "HPKE Base mode setup for a receiver.

@param o_ctx The encryption context to initialize.
@param enc Pointer to 32 bytes where the encapsulated key is read from.
@param skR Pointer to 32 bytes where the recipient's secret key is read from.
@param infolen Length of the info string.
@param info Pointer to `infolen` bytes of info string.

@returns 0 on success, non-zero on failure."]
let setupBaseR = hpke_setupBaseR_higher #cs True IHK.hkdf_expand512 IHK.hkdf_extract512 IDH.dh_c51 IHK.hkdf_expand256 IHK.hkdf_extract256 IDH.secret_to_public_c51

[@@ Comment "HPKE single-shot seal (encrypt).

@param skE Pointer to 32 bytes where the ephemeral secret key is read from.
@param pkR Pointer to 32 bytes where the recipient's public key is read from.
@param infolen Length of the info string.
@param info Pointer to `infolen` bytes of info string.
@param aadlen Length of the associated data.
@param aad Pointer to `aadlen` bytes of associated data.
@param plainlen Length of the plaintext.
@param plain Pointer to `plainlen` bytes of plaintext.
@param o_enc Pointer to 32 bytes where the encapsulated key is written to.
@param o_ct Pointer to `plainlen` + 16 bytes where the ciphertext and tag are written to.

@returns 0 on success, non-zero on failure."]
let sealBase = hpke_sealBase_higher #cs True IAEAD.aead_encrypt_cp256 setupBaseS

[@@ Comment "HPKE single-shot open (decrypt).

PRECONDITION: `ctlen` must be at least 16 (the tag length).

@param pkE Pointer to 32 bytes where the ephemeral public key is read from.
@param skR Pointer to 32 bytes where the recipient's secret key is read from.
@param infolen Length of the info string.
@param info Pointer to `infolen` bytes of info string.
@param aadlen Length of the associated data.
@param aad Pointer to `aadlen` bytes of associated data.
@param ctlen Length of the ciphertext (including the 16-byte tag). Must be at least 16.
@param ct Pointer to `ctlen` bytes of ciphertext.
@param o_pt Pointer to `ctlen` - 16 bytes where the plaintext is written to.

@returns 0 on success, non-zero on failure (e.g. authentication failure)."]
let openBase = hpke_openBase_higher #cs True IAEAD.aead_decrypt_cp256 setupBaseR
