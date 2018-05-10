module Crypto.Indexing

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

type rw =
  | Reader
  | Writer

type macAlg =
  | POLY1305
  | GHASH

type cipherAlg =
  | AES128
  | AES256
  | CHACHA20

// References:
//  - RFC 7539 for the AEAD algorithm
//  - RFC 7905 for ChaCha20_Poly1305 TLS ciphersuites
type aeadAlg =
  | AES_128_GCM
  | AES_256_GCM
  | CHACHA20_POLY1305

type aesImpl =
  | ValeAES
  | HaclAES

val id:Type0

val aeadAlg_of_id: i:id -> Tot aeadAlg

val macAlg_of_id: i:id -> Tot macAlg

val cipherAlg_of_id: i:id -> Tot cipherAlg

val aesImpl_of_id: i:id -> Tot aesImpl

val aeadAlg_cipherAlg: i:id -> Lemma
  (requires True)
  (ensures
    ((aeadAlg_of_id i == AES_128_GCM ==> cipherAlg_of_id i == AES128) /\
     (aeadAlg_of_id i == AES_256_GCM ==> cipherAlg_of_id i == AES256) /\
     (aeadAlg_of_id i == CHACHA20_POLY1305 ==> cipherAlg_of_id i == CHACHA20)))

val testId: a:aeadAlg -> Tot (i:id{aeadAlg_of_id i = a})
