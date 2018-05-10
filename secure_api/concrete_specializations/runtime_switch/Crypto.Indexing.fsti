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

// This allows a C caller to allocate an [id] and make its own decisions on the
// choice of AEAD algorithm and AES implementation.
type id = {
  aeadAlg: aeadAlg;
  aesImpl: aesImpl;
}

inline_for_extraction
let aeadAlg_of_id i = i.aeadAlg

inline_for_extraction
let macAlg_of_id i =
  match i.aeadAlg with
  | AES_128_GCM       -> GHASH
  | AES_256_GCM       -> GHASH
  | CHACHA20_POLY1305 -> POLY1305

inline_for_extraction
let cipherAlg_of_id i =
  match i.aeadAlg with
  | AES_128_GCM       -> AES128
  | AES_256_GCM       -> AES256
  | CHACHA20_POLY1305 -> CHACHA20

inline_for_extraction
let aesImpl_of_id (i:id) =
  i.aesImpl

let aeadAlg_cipherAlg: i:id -> Lemma
  (requires True)
  (ensures
    ((aeadAlg_of_id i == AES_128_GCM ==> cipherAlg_of_id i == AES128) /\
     (aeadAlg_of_id i == AES_256_GCM ==> cipherAlg_of_id i == AES256) /\
     (aeadAlg_of_id i == CHACHA20_POLY1305 ==> cipherAlg_of_id i == CHACHA20)))
  =
    fun (i: id) -> ()

// This is just a test id to abide by the requirements of the interface, but a C
// client can pick anything.
let testId (a:aeadAlg): Tot (i:id{aeadAlg_of_id i = a}) = { aeadAlg = a; aesImpl = HaclAES }
