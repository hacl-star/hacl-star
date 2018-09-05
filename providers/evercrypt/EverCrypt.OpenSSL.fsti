module EverCrypt.OpenSSL

open EverCrypt.Helpers
open EverCrypt.Specs
open FStar.HyperStack.ST

/// An OpenSSL provider that implements a subset of EverCrypt.fsti

val random_init: unit ->
  ST uint32_t random_init_pre random_init_post

val random_sample: len:uint32_t -> out:uint8_p ->
  ST unit random_sample_pre random_sample_post

val random_cleanup: unit ->
  ST unit random_cleanup_pre random_cleanup_post

val aes128_gcm_encrypt: key:uint8_p -> iv:uint8_p ->
  ad:uint8_p -> adlen:uint32_t ->
  plain:uint8_p -> len:uint32_t ->
  cipher: uint8_p -> tag:uint8_p ->
  Stack unit aes128_gcm_encrypt_pre aes128_gcm_encrypt_post

val aes128_gcm_decrypt: key:uint8_p -> iv:uint8_p ->
  ad:uint8_p -> adlen:uint32_t ->
  plain:uint8_p -> len:uint32_t ->
  cipher: uint8_p -> tag:uint8_p ->
  Stack uint32_t aes128_gcm_decrypt_pre aes128_gcm_decrypt_post

val aes256_gcm_encrypt: key:uint8_p -> iv:uint8_p ->
  ad:uint8_p -> adlen:uint32_t ->
  plain:uint8_p -> len:uint32_t ->
  cipher: uint8_p -> tag:uint8_p ->
  Stack unit aes256_gcm_encrypt_pre aes256_gcm_encrypt_post

val aes256_gcm_decrypt: key:uint8_p -> iv:uint8_p ->
  ad:uint8_p -> adlen:uint32_t ->
  plain:uint8_p -> len:uint32_t ->
  cipher: uint8_p -> tag:uint8_p ->
  Stack uint32_t aes256_gcm_decrypt_pre aes256_gcm_decrypt_post

val chacha20_poly1305_encrypt: key:uint8_p -> iv:uint8_p ->
  ad:uint8_p -> adlen:uint32_t ->
  plain:uint8_p -> len:uint32_t ->
  cipher: uint8_p -> tag:uint8_p ->
  Stack unit chacha20_poly1305_encrypt_pre chacha20_poly1305_encrypt_post

val chacha20_poly1305_decrypt: key:uint8_p -> iv:uint8_p ->
  ad:uint8_p -> adlen:uint32_t ->
  plain:uint8_p -> len:uint32_t ->
  cipher: uint8_p -> tag:uint8_p ->
  Stack uint32_t chacha20_poly1305_decrypt_pre chacha20_poly1305_decrypt_post

type alg =
  | AES128_GCM
  | AES256_GCM
  | CHACHA20_POLY1305

val aead_create: alg:alg -> key:uint8_p ->
  St Dyn.dyn

val aead_encrypt: key:Dyn.dyn -> iv:uint8_p ->
  ad:uint8_p -> adlen:uint32_t ->
  plain:uint8_p -> len:uint32_t ->
  cipher: uint8_p -> tag:uint8_p ->
  St unit

val aead_decrypt: key:Dyn.dyn -> iv:uint8_p ->
  ad:uint8_p -> adlen:uint32_t ->
  plain:uint8_p -> len:uint32_t ->
  cipher: uint8_p -> tag:uint8_p ->
  St uint32_t

val aead_free: key:Dyn.dyn ->
  St unit

/// DH

val dh_load_group:
  dh_p: uint8_p ->
  dh_p_len: uint32_t ->
  dh_g: uint8_p ->
  dh_g_len: uint32_t ->
  dh_q: uint8_p ->
  dh_q_len: uint32_t ->
  ST Dyn.dyn
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> modifies_none h0 h1)

val dh_free_group:
  st: Dyn.dyn ->
  ST unit
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> modifies_none h0 h1)

val dh_keygen:
  st: Dyn.dyn ->
  out: uint8_p ->
  ST uint32_t
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> modifies_none h0 h1)
  
val dh_compute:
  st: Dyn.dyn ->
  public: uint8_p ->
  public_len: uint32_t ->
  out: uint8_p ->
  ST uint32_t
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> modifies_none h0 h1)

/// ECDH

type ec_curve =
  | ECC_P256
  | ECC_P384
  | ECC_P521
  | ECC_X25519
  | ECC_X448

val ecdh_load_curve:
  g: ec_curve ->
  ST Dyn.dyn
  (requires fun h0 -> False)
  (ensures fun h0 _ h1 -> True)

val ecdh_free_curve:
  st: Dyn.dyn ->
  ST unit
  (requires fun h0 -> False)
  (ensures fun h0 _ h1 -> True)

val ecdh_keygen:
  st: Dyn.dyn ->
  outx: uint8_p ->
  outy: uint8_p ->
  ST unit
  (requires fun h0 -> False)
  (ensures fun h0 _ h1 -> True)

val ecdh_compute:
  st: Dyn.dyn ->
  inx: uint8_p ->
  iny: uint8_p ->
  out: uint8_p ->
  ST uint32_t
  (requires fun h0 -> False)
  (ensures fun h0 _ h1 -> True)

