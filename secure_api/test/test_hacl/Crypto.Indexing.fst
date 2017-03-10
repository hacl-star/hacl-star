module Crypto.Indexing

abstract type id0 = aeadAlg
let id : Type0 = id0

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

inline_for_extraction let aesImpl_of_id (i:id) =
  HaclAES

let testId (a:aeadAlg) = a

