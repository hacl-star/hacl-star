module EverCrypt

open FStar.HyperStack.ST
open EverCrypt.Helpers
open EverCrypt.Specs

module LB = LowStar.Buffer

///  SHA256

/// Incremental API
val sha256_init: state:uint32_p ->
  Stack unit sha256_init_pre sha256_init_post
val sha256_update: state:uint32_p -> data:uint8_p ->
  Stack unit sha256_update_pre sha256_update_post
val sha256_update_multi: state:uint32_p -> data:uint8_p -> n:uint32_t ->
  Stack unit sha256_update_multi_pre sha256_update_multi_post
val sha256_update_last: state:uint32_p -> data:uint8_p -> n:uint32_t ->
  Stack unit sha256_update_last_pre sha256_update_last_post
val sha256_finish: state:uint32_p -> data:uint8_p ->
  Stack unit sha256_finish_pre sha256_finish_post

/// Standalone API
val sha256_hash: dst:uint8_p -> src:uint8_p -> len:uint32_t ->
  Stack unit sha256_hash_pre sha256_hash_post


///  SHA384

/// Incremental API
val sha384_init: state:uint64_p ->
  Stack unit sha384_init_pre sha384_init_post
val sha384_update: state:uint64_p -> data:uint8_p ->
  Stack unit sha384_update_pre sha384_update_post
val sha384_update_multi: state:uint64_p -> data:uint8_p -> n:uint32_t ->
  Stack unit sha384_update_multi_pre sha384_update_multi_post
val sha384_update_last: state:uint64_p -> data:uint8_p -> n:uint32_t ->
  Stack unit sha384_update_last_pre sha384_update_last_post
val sha384_finish: state:uint64_p -> data:uint8_p ->
  Stack unit sha384_finish_pre sha384_finish_post

/// Standalone API
val sha384_hash: dst:uint8_p -> src:uint8_p -> len:uint32_t ->
  Stack unit sha384_hash_pre sha384_hash_post


///  SHA512

/// Incremental API
val sha512_init: state:uint64_p ->
  Stack unit sha512_init_pre sha512_init_post
val sha512_update: state:uint64_p -> data:uint8_p ->
  Stack unit sha512_update_pre sha512_update_post
val sha512_update_multi: state:uint64_p -> data:uint8_p -> n:uint32_t ->
  Stack unit sha512_update_multi_pre sha512_update_multi_post
val sha512_update_last: state:uint64_p -> data:uint8_p -> n:uint32_t ->
  Stack unit sha512_update_last_pre sha512_update_last_post
val sha512_finish: state:uint64_p -> data:uint8_p ->
  Stack unit sha512_finish_pre sha512_finish_post

/// Standalone API
val sha512_hash: dst:uint8_p -> src:uint8_p -> len:uint32_t ->
  Stack unit sha512_hash_pre sha512_hash_post

/// Curve25519

val x25519: dst:uint8_p -> secret:uint8_p -> base:uint8_p ->
  Stack unit curve_x25519_pre curve_x25519_post

/// AES block function

val aes128_key_s: Type0

[@(CPrologue "#ifndef __EverCrypt_aes128_key_s\ntypedef struct EverCrypt_aes128_key_s EverCrypt_aes128_key_s;\n#endif")]
let aes128_key = LB.pointer aes128_key_s

val aes128_create: key:uint8_p ->
  ST aes128_key aes128_create_pre aes128_create_post

val aes128_compute: key:aes128_key ->
  plain: uint8_p -> cipher:uint8_p ->
  ST unit aes128_compute_pre aes128_compute_post

val aes128_free: aes128_key ->
  ST unit aes128_free_pre aes128_free_post

val aes256_key_s : Type0

[@(CPrologue "#ifndef __EverCrypt_aes256_key_s\ntypedef struct EverCrypt_aes256_key_s EverCrypt_aes256_key_s;\n#endif")]
let aes256_key = LB.pointer aes256_key_s

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
