module EverCrypt.BCrypt

open EverCrypt.Helpers
open EverCrypt.Specs
open FStar.HyperStack.ST

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

type alg =
  | AES128_GCM
  | AES256_GCM

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
