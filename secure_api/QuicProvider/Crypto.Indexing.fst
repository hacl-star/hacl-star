module Crypto.Indexing

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

// This file is specialized for QUIC
// We only use the hardware-accelerated AES

type id0 = aeadAlg
let id = id0

inline_for_extraction let aeadAlg_of_id i = i

inline_for_extraction let macAlg_of_id i =
  match i with
  | AES_128_GCM       -> GHASH
  | AES_256_GCM       -> GHASH
  | CHACHA20_POLY1305 -> POLY1305

inline_for_extraction let cipherAlg_of_id i =
  match i with
  | AES_128_GCM       -> AES128
  | AES_256_GCM       -> AES256
  | CHACHA20_POLY1305 -> CHACHA20

inline_for_extraction let aesImpl_of_id (i:id) = ValeAES
let aeadAlg_cipherAlg i = ()
let testId (a:aeadAlg) = a

