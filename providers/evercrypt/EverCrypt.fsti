module EverCrypt

open FStar.HyperStack.ST
open EverCrypt.Helpers
open EverCrypt.Specs

module B = LowStar.Buffer

/// Hash algorithms

include EverCrypt.Hash

/// Curve

val x25519: dst:uint8_p -> secret:uint8_p -> base:uint8_p ->
  Stack unit curve_x25519_pre curve_x25519_post

/// AES block function

[@CAbstractStruct]
val aes128_key_s: Type0

let aes128_key = B.pointer aes128_key_s

val aes128_create: key:uint8_p ->
  ST aes128_key aes128_create_pre aes128_create_post

val aes128_compute: key:aes128_key ->
  plain: uint8_p -> cipher:uint8_p ->
  ST unit aes128_compute_pre aes128_compute_post

val aes128_free: aes128_key ->
  ST unit aes128_free_pre aes128_free_post

[@CAbstractStruct]
val aes256_key_s : Type0

let aes256_key = B.pointer aes256_key_s

val aes256_create: key:uint8_p ->
  ST aes256_key aes256_create_pre aes256_create_post

val aes256_compute: key:aes256_key ->
  plain: uint8_p -> cipher:uint8_p ->
  ST unit aes256_compute_pre aes256_compute_post

val aes256_free: aes256_key ->
  ST unit aes256_free_pre aes256_free_post

/// ChaCha20

val chacha20: key:uint8_p -> iv:uint8_p -> ctr: uint32_t ->
  plain: uint8_p -> len: uint32_t -> cipher: uint8_p ->
  Stack unit chacha20_pre chacha20_post

/// AES-GCM

val aes128_gcm_encrypt: key:uint8_p -> iv:uint8_p ->
  ad:uint8_p -> adlen:uint32_t ->
  plain:uint8_p -> len:uint32_t ->
  cipher: uint8_p -> tag:uint8_p ->
  ST unit aes256_gcm_encrypt_pre aes256_gcm_encrypt_post

val aes128_gcm_decrypt: key:uint8_p -> iv:uint8_p ->
  ad:uint8_p -> adlen:uint32_t ->
  plain:uint8_p -> len:uint32_t ->
  cipher: uint8_p -> tag:uint8_p ->
  ST uint32_t aes128_gcm_decrypt_pre aes128_gcm_decrypt_post

val aes256_gcm_encrypt: key:uint8_p -> iv:uint8_p ->
  ad:uint8_p -> adlen:uint32_t ->
  plain:uint8_p -> len:uint32_t ->
  cipher: uint8_p -> tag:uint8_p ->
  ST unit aes256_gcm_encrypt_pre aes256_gcm_encrypt_post

val aes256_gcm_decrypt: key:uint8_p -> iv:uint8_p ->
  ad:uint8_p -> adlen:uint32_t ->
  plain:uint8_p -> len:uint32_t ->
  cipher: uint8_p -> tag:uint8_p ->
  ST uint32_t aes256_gcm_decrypt_pre aes256_gcm_decrypt_post

/// Chacha20-Poly1305

val chacha20_poly1305_encrypt: key:uint8_p -> iv:uint8_p ->
  ad:uint8_p -> adlen:uint32_t ->
  plain:uint8_p -> len:uint32_t ->
  cipher: uint8_p -> tag:uint8_p ->
  ST unit chacha20_poly1305_encrypt_pre chacha20_poly1305_encrypt_post

val chacha20_poly1305_decrypt: key:uint8_p -> iv:uint8_p ->
  ad:uint8_p -> adlen:uint32_t ->
  plain:uint8_p -> len:uint32_t ->
  cipher: uint8_p -> tag:uint8_p ->
  ST uint32_t chacha20_poly1305_decrypt_pre chacha20_poly1305_decrypt_post

/// AEAD

type aead_alg =
  | AES128_GCM
  | AES256_GCM
  | CHACHA20_POLY1305

val aead_state_s: Type0

[@(CPrologue "#ifndef __EverCrypt_aead_state_s\ntypedef struct EverCrypt_aead_state_s EverCrypt_aead_state_s;\n#endif")]
let aead_state = B.pointer aead_state_s

val aead_create: alg:aead_alg -> key:uint8_p ->
  ST aead_state aead_create_pre aead_create_post

val aead_encrypt: key:aead_state -> iv:uint8_p ->
  ad:uint8_p -> adlen:uint32_t ->
  plain:uint8_p -> len:uint32_t ->
  cipher:uint8_p -> tag:uint8_p ->
  ST unit aead_encrypt_pre aead_encrypt_post

val aead_decrypt: key:aead_state -> iv:uint8_p ->
  ad:uint8_p -> adlen:uint32_t ->
  plain:uint8_p -> len:uint32_t ->
  cipher:uint8_p -> tag:uint8_p ->
  ST uint32_t aead_decrypt_pre aead_decrypt_post

val aead_free: aead_state ->
  ST unit aead_free_pre aead_free_post
