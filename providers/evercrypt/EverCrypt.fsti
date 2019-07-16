module EverCrypt

open FStar.HyperStack.ST
open EverCrypt.Helpers
open EverCrypt.Specs

module B = LowStar.Buffer

/// The EverCrypt verified cryptographic library
/// --------------------------------------------
///
/// This top-level module brings into scope all the components of EverCrypt.

include EverCrypt.Hash
include EverCrypt.HMAC
include EverCrypt.HKDF
include EverCrypt.Poly1305
include EverCrypt.Curve25519
include EverCrypt.Cipher

/// Legacy, deprecated
/// ------------------
///
/// Unverified, legacy wrappers calling into old HACL* code. Clients should
/// abandon these in favor of the verified, properly-specified modules above.

/// Random sampling

val random_init: unit ->
  ST uint32_t random_init_pre random_init_post

val random_sample: len:uint32_t -> out:uint8_p ->
  ST unit random_sample_pre random_sample_post

val random_cleanup: unit ->
  ST unit random_cleanup_pre random_cleanup_post

/// AES block function

[@CAbstractStruct]
val aes128_key_s: Type0

let aes128_key = B.pointer aes128_key_s

[@ (deprecated "Please use EverCrypt_CTR.h (from C) or EverCrypt.CTR.fsti (from F*) ")]
val aes128_create: key:uint8_p ->
  ST aes128_key aes128_create_pre aes128_create_post

[@ (deprecated "Please use EverCrypt_CTR.h (from C) or EverCrypt.CTR.fsti (from F*) ")]
val aes128_compute: key:aes128_key ->
  plain: uint8_p -> cipher:uint8_p ->
  ST unit aes128_compute_pre aes128_compute_post

[@ (deprecated "Please use EverCrypt_CTR.h (from C) or EverCrypt.CTR.fsti (from F*) ")]
val aes128_free: aes128_key ->
  ST unit aes128_free_pre aes128_free_post

[@CAbstractStruct]
val aes256_key_s : Type0

let aes256_key = B.pointer aes256_key_s

[@ (deprecated "Please use EverCrypt_CTR.h (from C) or EverCrypt.CTR.fsti (from F*) ")]
val aes256_create: key:uint8_p ->
  ST aes256_key aes256_create_pre aes256_create_post

[@ (deprecated "Please use EverCrypt_CTR.h (from C) or EverCrypt.CTR.fsti (from F*) ")]
val aes256_compute: key:aes256_key ->
  plain: uint8_p -> cipher:uint8_p ->
  ST unit aes256_compute_pre aes256_compute_post

[@ (deprecated "Please use EverCrypt_CTR.h (from C) or EverCrypt.CTR.fsti (from F*) ")]
val aes256_free: aes256_key ->
  ST unit aes256_free_pre aes256_free_post


/// AES-GCM

[@ (deprecated "Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")]
val aes128_gcm_encrypt: key:uint8_p -> iv:uint8_p ->
  ad:uint8_p -> adlen:uint32_t ->
  plain:uint8_p -> len:uint32_t ->
  cipher: uint8_p -> tag:uint8_p ->
  ST unit aes256_gcm_encrypt_pre aes256_gcm_encrypt_post

[@ (deprecated "Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")]
val aes128_gcm_decrypt: key:uint8_p -> iv:uint8_p ->
  ad:uint8_p -> adlen:uint32_t ->
  plain:uint8_p -> len:uint32_t ->
  cipher: uint8_p -> tag:uint8_p ->
  ST uint32_t aes128_gcm_decrypt_pre aes128_gcm_decrypt_post

[@ (deprecated "Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")]
val aes256_gcm_encrypt: key:uint8_p -> iv:uint8_p ->
  ad:uint8_p -> adlen:uint32_t ->
  plain:uint8_p -> len:uint32_t ->
  cipher: uint8_p -> tag:uint8_p ->
  ST unit aes256_gcm_encrypt_pre aes256_gcm_encrypt_post

[@ (deprecated "Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")]
val aes256_gcm_decrypt: key:uint8_p -> iv:uint8_p ->
  ad:uint8_p -> adlen:uint32_t ->
  plain:uint8_p -> len:uint32_t ->
  cipher: uint8_p -> tag:uint8_p ->
  ST uint32_t aes256_gcm_decrypt_pre aes256_gcm_decrypt_post

/// Agile Block and Stream Ciphers (adapted from CoreCrypto, TBC)

type block_cipher_alg =
  | AES128_CBC
  | AES256_CBC
  | TDES_EDE_CBC

let block_cipher_keyLen = function
  | AES128_CBC   -> 16ul
  | AES256_CBC   -> 32ul
  | TDES_EDE_CBC  -> 24ul

let block_cipher_blockLen = function
  | AES128_CBC   -> 16ul
  | AES256_CBC   -> 16ul
  | TDES_EDE_CBC ->  8ul

type stream_cipher_alg = 
  | RC4_128

/// Agile AEAD

type aead_alg =
  | AES128_GCM
  | AES256_GCM
  | CHACHA20_POLY1305
  // the algorithms below are used in TLS 1.3 but not yet supported by
  // EverCrypt or miTLS; they are included e.g. for parsing
  | AES128_CCM  // "Counter with CBC-Message Authentication Code"
  | AES256_CCM
  | AES128_CCM8 // variant with truncated 8-byte tags
  | AES256_CCM8

[@ (deprecated "Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")]
let supported_aead_alg (a:aead_alg): GTot bool = 
  match a with 
  | AES128_GCM
  | AES256_GCM
  | CHACHA20_POLY1305 -> true
  | _ -> false

[@ (deprecated "Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")]
let aead_keyLen = function
  | AES128_GCM        -> 16ul
  | AES256_GCM        -> 32ul
  | CHACHA20_POLY1305 -> 32ul
  | AES128_CCM        -> 16ul
  | AES128_CCM8       -> 16ul
  | AES256_CCM        -> 32ul
  | AES256_CCM8       -> 32ul

[@ (deprecated "Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")]
let aead_tagLen = function
  | AES128_CCM8       ->  8ul
  | AES256_CCM8       ->  8ul
  | AES128_GCM        -> 16ul
  | AES256_GCM        -> 16ul
  | CHACHA20_POLY1305 -> 16ul
  | AES128_CCM        -> 16ul
  | AES256_CCM        -> 16ul

[@ (deprecated "Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")]
let aead_ivLen (a:aead_alg) = 12ul


[@CAbstractStruct]
val aead_state_s: Type0

let aead_state = B.pointer aead_state_s

[@ (deprecated "Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")]
val aead_create: a:aead_alg {supported_aead_alg a} -> key:uint8_p ->
  ST aead_state aead_create_pre aead_create_post

[@ (deprecated "Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")]
val aead_encrypt: key:aead_state -> iv:uint8_p ->
  ad:uint8_p -> adlen:uint32_t ->
  plain:uint8_p -> len:uint32_t ->
  cipher:uint8_p -> tag:uint8_p ->
  ST unit aead_encrypt_pre aead_encrypt_post

[@ (deprecated "Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")]
val aead_decrypt: key:aead_state -> iv:uint8_p ->
  ad:uint8_p -> adlen:uint32_t ->
  plain:uint8_p -> len:uint32_t ->
  cipher:uint8_p -> tag:uint8_p ->
  ST uint32_t aead_decrypt_pre aead_decrypt_post

[@ (deprecated "Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")]
val aead_free: aead_state ->
  ST unit aead_free_pre aead_free_post

/// DH

[@CAbstractStruct]
val dh_state_s: Type0

let dh_state = B.pointer dh_state_s

val dh_load_group:
  dh_p: uint8_p ->
  dh_p_len: uint32_t ->
  dh_g: uint8_p ->
  dh_g_len: uint32_t ->
  dh_q: uint8_p ->
  dh_q_len: uint32_t ->
  ST dh_state
  (requires fun h0 -> False)
  (ensures fun h0 _ h1 -> True)

val dh_free_group:
  st: dh_state ->
  ST unit
  (requires fun h0 -> False)
  (ensures fun h0 _ h1 -> True)

val dh_keygen:
  st: dh_state ->
  out: uint8_p ->
  ST uint32_t
  (requires fun h0 -> False)
  (ensures fun h0 _ h1 -> True)

val dh_compute:
  st: dh_state ->
  public: uint8_p ->
  public_len: uint32_t ->
  out: uint8_p ->
  ST uint32_t
  (requires fun h0 -> False)
  (ensures fun h0 _ h1 -> True)

/// ECDH

type ec_curve =
  | ECC_P256
  | ECC_P384
  | ECC_P521
  | ECC_X25519
  | ECC_X448

[@CAbstractStruct]
val ecdh_state_s: Type0

let ecdh_state = B.pointer ecdh_state_s

val ecdh_load_curve:
  g: ec_curve ->
  ST ecdh_state
  (requires fun h0 -> False)
  (ensures fun h0 _ h1 -> True)

val ecdh_free_curve:
  st: ecdh_state ->
  ST unit
  (requires fun h0 -> False)
  (ensures fun h0 _ h1 -> True)

val ecdh_keygen:
  st: ecdh_state ->
  outx: uint8_p ->
  outy: uint8_p ->
  ST unit
  (requires fun h0 -> False)
  (ensures fun h0 _ h1 -> True)

val ecdh_compute:
  st: ecdh_state ->
  inx: uint8_p ->
  iny: uint8_p ->
  out: uint8_p ->
  ST uint32_t
  (requires fun h0 -> False)
  (ensures fun h0 _ h1 -> True)
