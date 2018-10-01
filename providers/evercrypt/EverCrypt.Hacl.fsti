module EverCrypt.Hacl

open EverCrypt.Helpers
open EverCrypt.Specs
open FStar.HyperStack.ST

/// This module essentially repeats EverCrypt, but without implicit
/// multiplexing. Eventually, the specs should be shared between Hacl and
/// EverCrypt.


/// Curve

val x25519: dst:uint8_p -> secret:uint8_p -> base:uint8_p ->
  Stack unit curve_x25519_pre curve_x25519_post

/// AES block function

val aes128_keyExpansion: key:uint8_p -> w:uint8_p -> sb:uint8_p ->
  Stack unit aes128_create_pre aes128_create_post
val aes128_cipher: cipher:uint8_p -> plain:uint8_p -> w:uint8_p -> sb:uint8_p ->
  Stack unit aes128_compute_pre aes128_compute_post

val aes256_keyExpansion: key:uint8_p -> w:uint8_p -> sb:uint8_p ->
  Stack unit aes256_create_pre aes256_create_post
val aes256_cipher: cipher:uint8_p -> plain:uint8_p -> w:uint8_p -> sb:uint8_p ->
  Stack unit aes256_compute_pre aes256_compute_post

/// ChaCha20

val chacha20: key:uint8_p -> iv:uint8_p -> ctr: uint32_t ->
  plain: uint8_p -> len: uint32_t -> cipher: uint8_p ->
  Stack unit chacha20_pre chacha20_post

/// Chacha20-Poly1305

val chacha20_poly1305_encrypt: c:uint8_p -> mac:uint8_p -> m:uint8_p -> m_len:uint32_t ->
  aad:uint8_p -> aad_len:uint32_t -> k:uint8_p -> n:uint8_p ->
  Stack uint32_t chacha20_poly1305_encrypt_pre chacha20_poly1305_encrypt_post
val chacha20_poly1305_decrypt: m:uint8_p -> c:uint8_p -> m_len:uint32_t -> mac:uint8_p ->
  aad:uint8_p -> aad_len:uint32_t -> k:uint8_p -> n:uint8_p ->
  Stack uint32_t chacha20_poly1305_decrypt_pre chacha20_poly1305_decrypt_post
