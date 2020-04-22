module Hacl.HPKE.Interface.AEAD

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.Buffer

friend Spec.Agile.AEAD

/// These two functions will never be extracted, they are only an interface
/// boundary for the tactic performing instantiations.
/// In other files, it is exposed as an assume val, but for AEAD, we need an fsti
/// since we need to friend Spec.Agile.AEAD to perform the instantiations below,
/// and assume val are forbidden in interface files
let aead_encrypt #cs = admit()
let aead_decrypt #cs = admit()

#set-options "--z3rlimit 60 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let aead_encrypt_cp32 =
  fun key nonce alen aad len input output ->
    Hacl.Chacha20Poly1305_32.aead_encrypt key nonce alen aad len input (sub output 0ul len) (sub output len 16ul)

inline_for_extraction noextract
let aead_decrypt_cp32 =
  fun key nonce alen aad len input output ->
    Hacl.Chacha20Poly1305_32.aead_decrypt key nonce alen aad len input (sub output 0ul len) (sub output len 16ul)

inline_for_extraction noextract
let aead_encrypt_cp128 =
  fun key nonce alen aad len input output ->
    Hacl.Chacha20Poly1305_128.aead_encrypt key nonce alen aad len input (sub output 0ul len) (sub output len 16ul)

inline_for_extraction noextract
let aead_decrypt_cp128 =
  fun key nonce alen aad len input output ->
    Hacl.Chacha20Poly1305_128.aead_decrypt key nonce alen aad len input (sub output 0ul len) (sub output len 16ul)

inline_for_extraction noextract
let aead_encrypt_cp256 =
  fun key nonce alen aad len input output ->
    Hacl.Chacha20Poly1305_256.aead_encrypt key nonce alen aad len input (sub output 0ul len) (sub output len 16ul)

inline_for_extraction noextract
let aead_decrypt_cp256 =
  fun key nonce alen aad len input output ->
    Hacl.Chacha20Poly1305_256.aead_decrypt key nonce alen aad len input (sub output 0ul len) (sub output len 16ul)
