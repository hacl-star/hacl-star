module Hacl.Core

open Hacl.Constants


//////////////////////////////////////////////////////////////////
//
// Hashing functions
//

let hash alg output data len =
  match alg with
  | SHA1 -> Hash.sha1 output data len
  | SHA2_224 -> Hash.sha2_224 output data len
  | SHA2_256 -> Hash.sha2_256 output data len
  | SHA2_384 -> Hash.sha2_384 output data len
  | SHA2_512 -> Hash.sha2_512 output data len
  | SHA3_224 -> Hash.sha3_224 output data len
  | SHA3_256 -> Hash.sha3_256 output data len
  | SHA3_384 -> Hash.sha3_384 output data len
  | SHA3_512 -> Hash.sha3_512 output data len

let hash_init alg output data len =
  match alg with
  | SHA1 -> Hash.sha1_init output data len
  | SHA2_224 -> Hash.sha2_224_init output data len
  | SHA2_256 -> Hash.sha2_256_init output data len
  | SHA2_384 -> Hash.sha2_384_init output data len
  | SHA2_512 -> Hash.sha2_512_init output data len
  | SHA3_224 -> Hash.sha3_224_init output data len
  | SHA3_256 -> Hash.sha3_256_init output data len
  | SHA3_384 -> Hash.sha3_384_init output data len
  | SHA3_512 -> Hash.sha3_512_init output data len

let hash_update alg output data len =
  match alg with
  | SHA1 -> Hash.sha1_update output data len
  | SHA2_224 -> Hash.sha2_224_update output data len
  | SHA2_256 -> Hash.sha2_256_update output data len
  | SHA2_384 -> Hash.sha2_384_update output data len
  | SHA2_512 -> Hash.sha2_512_update output data len
  | SHA3_224 -> Hash.sha3_224_update output data len
  | SHA3_256 -> Hash.sha3_256_update output data len
  | SHA3_384 -> Hash.sha3_384_update output data len
  | SHA3_512 -> Hash.sha3_512_update output data len

let hash_finish alg output data len =
  match alg with
  | SHA1 -> Hash.sha1_finish output data len
  | SHA2_224 -> Hash.sha2_224_finish output data len
  | SHA2_256 -> Hash.sha2_256_finish output data len
  | SHA2_384 -> Hash.sha2_384_finish output data len
  | SHA2_512 -> Hash.sha2_512_finish output data len
  | SHA3_224 -> Hash.sha3_224_finish output data len
  | SHA3_256 -> Hash.sha3_256_finish output data len
  | SHA3_384 -> Hash.sha3_384_finish output data len
  | SHA3_512 -> Hash.sha3_512_finish output data len


//////////////////////////////////////////////////////////////////
//
// Message authentication functions
//

let hmac alg output key keylen data len =
  match alg with
  | SHA1 -> Hmac.sha1 output key keylen data len
  | SHA2_224 -> Hmac.sha2_224 output key keylen data len
  | SHA2_256 -> Hmac.sha2_256 output key keylen data len
  | SHA2_384 -> Hmac.sha2_384 output key keylen data len
  | SHA2_512 -> Hmac.sha2_512 output key keylen data len
  | SHA3_224 -> Hmac.sha3_224 output key keylen data len
  | SHA3_256 -> Hmac.sha3_256 output key keylen data len
  | SHA3_384 -> Hmac.sha3_384 output key keylen data len
  | SHA3_512 -> Hmac.sha3_512 output key keylen data len

let hmac_init alg output key keylen data len =
  match alg with
  | SHA1 -> Hmac.sha1_init output key keylen data len
  | SHA2_224 -> Hmac.sha2_224_init output key keylen data len
  | SHA2_256 -> Hmac.sha2_256_init output key keylen data len
  | SHA2_384 -> Hmac.sha2_384_init output key keylen data len
  | SHA2_512 -> Hmac.sha2_512_init output key keylen data len
  | SHA3_224 -> Hmac.sha3_224_init output key keylen data len
  | SHA3_256 -> Hmac.sha3_256_init output key keylen data len
  | SHA3_384 -> Hmac.sha3_384_init output key keylen data len
  | SHA3_512 -> Hmac.sha3_512_init output key keylen data len

let hmac_update alg output key keylen data len =
  match alg with
  | SHA1 -> Hmac.sha1_update output key keylen data len
  | SHA2_224 -> Hmac.sha2_224_update output key keylen data len
  | SHA2_256 -> Hmac.sha2_256_update output key keylen data len
  | SHA2_384 -> Hmac.sha2_384_update output key keylen data len
  | SHA2_512 -> Hmac.sha2_512_update output key keylen data len
  | SHA3_224 -> Hmac.sha3_224_update output key keylen data len
  | SHA3_256 -> Hmac.sha3_256_update output key keylen data len
  | SHA3_384 -> Hmac.sha3_384_update output key keylen data len
  | SHA3_512 -> Hmac.sha3_512_update output key keylen data len

let hmac_finish alg output key keylen data len =
  match alg with
  | SHA1 -> Hmac.sha1_finish output key keylen data len
  | SHA2_224 -> Hmac.sha2_224_finish output key keylen data len
  | SHA2_256 -> Hmac.sha2_256_finish output key keylen data len
  | SHA2_384 -> Hmac.sha2_384_finish output key keylen data len
  | SHA2_512 -> Hmac.sha2_512_finish output key keylen data len
  | SHA3_224 -> Hmac.sha3_224_finish output key keylen data len
  | SHA3_256 -> Hmac.sha3_256_finish output key keylen data len
  | SHA3_384 -> Hmac.sha3_384_finish output key keylen data len
  | SHA3_512 -> Hmac.sha3_512_finish output key keylen data len


//////////////////////////////////////////////////////////////////
//
// Key derivation functions
//

let hkdf_extract alg prk salt saltlen ikm ikmlen =
  match alg with
  | HMAC_SHA1 -> Hkdf.hmac_sha1 prk salt saltlen ikm ikmlen
  | HMAC_SHA2_224 -> Hkdf.hmac_sha2_224 prk salt saltlen ikm ikmlen
  | HMAC_SHA2_256 -> Hkdf.hmac_sha2_256 prk salt saltlen ikm ikmlen
  | HMAC_SHA2_384 -> Hkdf.hmac_sha2_384 prk salt saltlen ikm ikmlen
  | HMAC_SHA2_512 -> Hkdf.hmac_sha2_512 prk salt saltlen ikm ikmlen
  | HMAC_SHA3_224 -> Hkdf.hmac_sha3_224 prk salt saltlen ikm ikmlen
  | HMAC_SHA3_256 -> Hkdf.hmac_sha3_256 prk salt saltlen ikm ikmlen
  | HMAC_SHA3_384 -> Hkdf.hmac_sha3_384 prk salt saltlen ikm ikmlen
  | HMAC_SHA3_512 -> Hkdf.hmac_sha3_512 prk salt saltlen ikm ikmlen

let hkdf_expand alg okm prk prklen info infolen l =
  match alg with
  | HMAC_SHA1 -> Hkdf.hmac_sha1 okm prk prklen info infolen l
  | HMAC_SHA2_224 -> Hkdf.hmac_sha2_224 okm prk prklen info infolen l
  | HMAC_SHA2_256 -> Hkdf.hmac_sha2_256 okm prk prklen info infolen l
  | HMAC_SHA2_384 -> Hkdf.hmac_sha2_384 okm prk prklen info infolen l
  | HMAC_SHA2_512 -> Hkdf.hmac_sha2_512 okm prk prklen info infolen l
  | HMAC_SHA3_224 -> Hkdf.hmac_sha3_224 okm prk prklen info infolen l
  | HMAC_SHA3_256 -> Hkdf.hmac_sha3_256 okm prk prklen info infolen l
  | HMAC_SHA3_384 -> Hkdf.hmac_sha3_384 okm prk prklen info infolen l
  | HMAC_SHA3_512 -> Hkdf.hmac_sha3_512 okm prk prklen info infolen l



//////////////////////////////////////////////////////////////////
//
//  Other mathematical operations
//

let maths_gf128_add a b = GCM.gf128_add a b
let maths_gf128_mul a b = GCM.gf128_mul a b


//////////////////////////////////////////////////////////////////
//
// Other message authentication functions
//

let mac_poly1305 hash msg len key =
  poly1305_mac hash msg len key


//////////////////////////////////////////////////////////////////
//
// Other schemes and AEAD functions
//

let symmetric_chacha20_encrypt ciphertext key counter nonce plaintext len = 
  Chacha20.chacha20_encrypt ciphertext key counter nonce plaintext len

let symmetric_chacha20_decrypt plaintext key counter nonce ciphertext len = 
  Chacha20.chacha20_decrypt plaintext key counter nonce ciphertext len


let aead_aes256_gcm_encrypt ciphertext tag key iv plaintext len ad adlen =
  AEAD.AES256_GCM.aead_encrypt ciphertext tag key iv plaintext len ad adlen

let aead_aes256_gcm_decrypt plaintext tag key iv ciphertext len ad adlen =
  AEAD.AES256_GCM.aead_decrypt plaintext tag key iv ciphertext len ad adlen


