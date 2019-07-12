module Spec.AEAD

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence


type algorithm =
  | AEAD_AES128_GCM
  | AEAD_Chacha20_Poly1305

inline_for_extraction
let size_key (a:algorithm) : Tot size_nat =
  match a with
  | AEAD_AES128_GCM -> 16
  | AEAD_Chacha20_Poly1305 -> 32

inline_for_extraction
let size_block (a:algorithm) : Tot size_nat =
  match a with
  | AEAD_AES128_GCM -> 16 // Spec.AES128_GCM.size_block
  | AEAD_Chacha20_Poly1305 -> 16 // Spec.Chacha20Poly1305.size_block

inline_for_extraction
let size_tag (a:algorithm) : Tot size_nat =
  match a with
  | AEAD_AES128_GCM -> 16 // Spec.AES128_GCM.size_tag
  | AEAD_Chacha20_Poly1305 -> 16 // Spec.Chacha20Poly1305.size_tag

inline_for_extraction
let size_nonce (a:algorithm) : Tot size_nat =
  match a with
  | AEAD_AES128_GCM -> 12 // Spec.AES128_GCM.size_nonce
  | AEAD_Chacha20_Poly1305 -> 12 // Spec.Chacha20Poly1305.size_nonce


inline_for_extraction
let padlen (a:algorithm) (x:size_nat) : size_nat =
  ((size_block a - x % (size_block a)) % (size_block a))


/// Types

type key (a:algorithm) = lbytes (size_key a)
type block (a:algorithm) = lbytes (size_block a)
type nonce (a:algorithm) = lbytes (size_nonce a)


/// API

val aead_encrypt:
    a: algorithm
  -> k: key a
  -> n: nonce a
  -> m: bytes{length m <= max_size_t
           /\ length m + size_block a <= max_size_t
           /\ length m + padlen a (length m) <= max_size_t}
  -> aad: bytes {length aad <= max_size_t /\ length aad + padlen a (length aad) <= max_size_t} ->
  Tot (lbytes (length m + size_tag a))

let aead_encrypt a k n m aad =
  match a with
  | AEAD_AES128_GCM -> Spec.AES128_GCM.aead_encrypt k n m aad
  | AEAD_Chacha20_Poly1305 -> Spec.Chacha20Poly1305.aead_encrypt k n m aad


val aead_decrypt:
    a: algorithm
  -> k: key a
  -> n: nonce a
  -> c: bytes{size_tag a <= length c /\ length c <= max_size_t}
  -> aad: bytes{length aad <= max_size_t
             /\ (length c + length aad) / 64 <= max_size_t
             /\ length aad + padlen a (length aad) <= max_size_t} ->
  Tot (option (lbytes (length c - size_tag a)))

let aead_decrypt a k n c aad =
  match a with
  | AEAD_AES128_GCM -> Spec.AES128_GCM.aead_decrypt k n c aad
  | AEAD_Chacha20_Poly1305 -> Spec.Chacha20Poly1305.aead_decrypt k n c aad
