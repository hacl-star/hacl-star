module EverCrypt.OpenSSL

open EverCrypt.Helpers
open EverCrypt.Specs
open FStar.HyperStack.ST

/// An OpenSSL provider that implements a subset of EverCrypt.fsti

/// AES-GCM

val aes256_gcm_encrypt: cipher: uint8_p -> tag:uint8_p -> key:uint8_p ->
  iv:uint8_p -> plaintext:uint8_p -> len: uint32_t ->
  ad:uint8_p -> adlen:uint32_t ->
    Stack unit aes256_gcm_encrypt_pre aes256_gcm_encrypt_post
