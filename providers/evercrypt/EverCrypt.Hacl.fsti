module EverCrypt.Hacl

open EverCrypt.Helpers
open EverCrypt.Specs
open FStar.HyperStack.ST

/// DEPRECATED MODULE -- resolves onto old-HACL modules at link-time via a
/// series of terrible hacks below. Use EverCrypt.AEAD for all new needs.

/// Curve

[@ (CPrologue "#define EverCrypt_Hacl_x25519 Hacl_Curve25519_crypto_scalarmult")]
val x25519: dst:uint8_p -> secret:uint8_p -> base:uint8_p ->
  Stack unit curve_x25519_pre curve_x25519_post

/// AES block function

[@ (CPrologue "#define EverCrypt_Hacl_aes128_mk_sbox Crypto_Symmetric_AES128_mk_sbox")]
val aes128_mk_sbox: sb:uint8_p ->
  Stack unit (fun _ -> true) (fun _ _ _ -> true)
[@ (CPrologue "#define EverCrypt_Hacl_aes128_keyExpansion Crypto_Symmetric_AES128_keyExpansion")]
val aes128_keyExpansion: key:uint8_p -> w:uint8_p -> sb:uint8_p ->
  Stack unit aes128_create_pre aes128_create_post
[@ (CPrologue "#define EverCrypt_Hacl_aes128_cipher Crypto_Symmetric_AES128_cipher")]
val aes128_cipher: cipher:uint8_p -> plain:uint8_p -> w:uint8_p -> sb:uint8_p ->
  Stack unit aes128_compute_pre aes128_compute_post

[@ (CPrologue "#define EverCrypt_Hacl_aes256_mk_sbox Crypto_Symmetric_AES_mk_sbox")]
val aes256_mk_sbox: sb:uint8_p ->
  Stack unit (fun _ -> true) (fun _ _ _ -> true)
[@ (CPrologue "#define EverCrypt_Hacl_aes256_keyExpansion Crypto_Symmetric_AES_keyExpansion")]
val aes256_keyExpansion: key:uint8_p -> w:uint8_p -> sb:uint8_p ->
  Stack unit aes256_create_pre aes256_create_post
[@ (CPrologue "#define EverCrypt_Hacl_aes256_cipher Crypto_Symmetric_AES_cipher")]
val aes256_cipher: cipher:uint8_p -> plain:uint8_p -> w:uint8_p -> sb:uint8_p ->
  Stack unit aes256_compute_pre aes256_compute_post

/// ChaCha20
[@ (CPrologue "#define EverCrypt_Hacl_chacha20(key, iv, ctr, plain, len, cipher) \
  Hacl_Chacha20_chacha20(cipher, plain, len, key, iv, ctr)")]
val chacha20: key:uint8_p -> iv:uint8_p -> ctr: uint32_t ->
  plain: uint8_p -> len: uint32_t -> cipher: uint8_p ->
  Stack unit chacha20_pre chacha20_post

/// Chacha20-Poly1305

[@ (CPrologue "#define EverCrypt_Hacl_chacha20_poly1305_encrypt Hacl_Chacha20Poly1305_aead_encrypt")]
val chacha20_poly1305_encrypt: c:uint8_p -> mac:uint8_p -> m:uint8_p -> m_len:uint32_t ->
  aad:uint8_p -> aad_len:uint32_t -> k:uint8_p -> n:uint8_p ->
  Stack uint32_t chacha20_poly1305_encrypt_pre chacha20_poly1305_encrypt_post
[@ (CPrologue "#define EverCrypt_Hacl_chacha20_poly1305_decrypt Hacl_Chacha20Poly1305_aead_decrypt")]
val chacha20_poly1305_decrypt: m:uint8_p -> c:uint8_p -> m_len:uint32_t -> mac:uint8_p ->
  aad:uint8_p -> aad_len:uint32_t -> k:uint8_p -> n:uint8_p ->
  Stack uint32_t chacha20_poly1305_decrypt_pre chacha20_poly1305_decrypt_post
