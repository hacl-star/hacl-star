module EverCrypt.Hacl

open EverCrypt.Helpers
open EverCrypt.Specs
open FStar.HyperStack.ST

/// DEPRECATED MODULE -- resolves onto old-HACL modules at link-time via a
/// series of terrible hacks below. Use EverCrypt.AEAD, EverCrypt.Poly1305, etc.
/// for all new needs.


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
