module EverCrypt

open FStar.HyperStack.ST
open EverCrypt.Helpers
open EverCrypt.Specs

include EverCrypt.Native

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
val sha384_update_last: state:uint64_p -> data:uint8_p -> n:uint64_t ->
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
val sha512_update_last: state:uint64_p -> data:uint8_p -> n:uint64_t ->
  Stack unit sha512_update_last_pre sha512_update_last_post
val sha512_finish: state:uint64_p -> data:uint8_p ->
  Stack unit sha512_finish_pre sha512_finish_post

/// Standalone API
val sha512_hash: dst:uint8_p -> src:uint8_p -> len:uint32_t ->
  Stack unit sha512_hash_pre sha512_hash_post


/// Curve

val x25519: dst:uint8_p -> secret:uint8_p -> base:uint8_p ->
  Stack unit curve_x25519_pre curve_x25519_post


/// AES-GCM

val aes256_gcm_encrypt: cipher: uint8_p -> tag:uint8_p -> key:uint8_p ->
  iv:uint8_p -> plaintext:uint8_p -> len: uint32_t ->
  ad:uint8_p -> adlen:uint32_t ->
    Stack unit aes256_gcm_encrypt_pre aes256_gcm_encrypt_post
