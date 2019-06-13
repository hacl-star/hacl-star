module Spec.Chacha20Poly1305

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

module Poly = Spec.Poly1305

(* RFC7539: https://tools.ietf.org/html/rfc7539#section-2.8 *)
#set-options "--max_fuel 0 --z3rlimit 30"

/// Constants

let size_key : size_nat =   32 (* in bytes *)
let size_nonce : size_nat = 12 (* in bytes *)
let size_block : size_nat = Poly.size_block
let size_tag : size_nat = size_block

/// Types

type key = lbytes size_key
type nonce = lbytes size_nonce
type tag = lbytes size_tag

/// Specification

val poly1305_padded:
    r_elem:Poly.felem
  -> text:bytes
  -> acc:Poly.felem ->
  Tot Poly.felem
let poly1305_padded r_elem text acc =
  let len = length text in
  let n = len / Poly.size_block in
  let r = len % Poly.size_block in
  let blocks = Seq.slice text 0 (n * Poly.size_block) in
  let rem = Seq.slice text (n * Poly.size_block) len in
  let acc = Poly.poly1305_update blocks acc r_elem in

  let tmp = create Poly.size_block (u8 0) in
  let tmp = update_sub tmp 0 r rem in
  // Only run the padded block if the initial text needed padding
  let acc = if r > 0 then Poly.poly1305_update1 r_elem Poly.size_block tmp acc else acc in
  acc

val poly1305_do:
    k:Poly.key
  -> m:bytes{length m <= maxint U64}
  -> aad:bytes{length aad <= maxint U64} ->
  Tot Poly.tag
let poly1305_do k m aad =
  let acc, r = Poly.poly1305_init k in
  let acc = poly1305_padded r aad acc in
  let acc = poly1305_padded r m acc in
  let aad_len8 = uint_to_bytes_le #U64 (u64 (length aad)) in
  let ciphertext_len8 = uint_to_bytes_le #U64 (u64 (length m)) in
  let block = aad_len8 @| ciphertext_len8 in
  let acc = Poly.poly1305_update1 r 16 block acc in
  Poly.poly1305_finish k acc

val aead_encrypt:
    k:key
  -> n:nonce
  -> m:bytes{length m <= max_size_t}
  -> aad:bytes{length aad <= maxint U64} ->
  Tot (res:bytes{length res == length m + Poly.size_block})
let aead_encrypt k n m aad =
  let cipher = Spec.Chacha20.chacha20_encrypt_bytes k n 1 m in
  let key0:lbytes 64 = Spec.Chacha20.chacha20_encrypt_bytes k n 0 (create 64 (u8 0)) in
  let poly_k = sub key0 0 32 in
  let mac = poly1305_do poly_k cipher aad in
  Seq.append cipher mac

val aead_decrypt:
    k:key
  -> n:nonce
  -> c:bytes{length c <= max_size_t}
  -> mac:tag
  -> aad:bytes{length aad <= maxint U64} ->
  Tot (option (lbytes (length c)))
let aead_decrypt k n cipher mac aad =
  let key0:lbytes 64 = Spec.Chacha20.chacha20_encrypt_bytes k n 0 (create 64 (u8 0)) in
  let poly_k = sub key0 0 32 in
  let computed_mac = poly1305_do poly_k cipher aad in
  if lbytes_eq computed_mac mac then
    let plain = Spec.Chacha20.chacha20_encrypt_bytes k n 1 cipher in
    Some plain
  else None
