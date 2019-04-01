module Spec.Chacha20Poly1305

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.RawIntTypes

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

let poly1305_padded
  (r_elem:Poly.felem)
  (len:size_nat) 
  (text:lbytes len) 
  (tmp:lbytes Poly.size_block) 
  (acc:Poly.felem) 
  : Tot (Poly.felem)
  = let n = len / Poly.size_block in
    let r = len % Poly.size_block in
    let blocks = sub text 0 (n * Poly.size_block) in
    let rem = sub text (n * Poly.size_block) r in
    let acc = Poly.poly blocks acc r_elem in
    let tmp = update_sub tmp 0 r rem in
    // Only run the padded block if the initial text needed padding
    let acc = if r > 0 then Poly.update1 r_elem Poly.size_block tmp acc else acc in
    acc

let poly1305_do
  (k:Poly.key)
  (len:size_nat{len <= max_size_t})
  (m:lbytes len)
  (aad_len:size_nat{(len + aad_len) / Spec.Chacha20.blocklen <= max_size_t})
  (aad:lbytes aad_len):
  Tot Poly.tag =
  let acc, r = Poly.poly1305_init k in
  let block = create Poly.size_block (u8 0) in
  let acc = poly1305_padded r aad_len aad block acc in
  let acc = poly1305_padded r len m block acc in
  let aad_len8 = uint_to_bytes_le #U64 (u64 aad_len) in
  let ciphertext_len8 = uint_to_bytes_le #U64 (u64 len) in
  let block = update_sub block 0 8 aad_len8 in
  let block = update_sub block 8 8 ciphertext_len8 in
  let acc = Poly.update1 r 16 block acc in
  Poly.finish k acc

val aead_encrypt:
    k:key
  -> n:nonce
  -> m: bytes{length m + size_block <= max_size_t}
  -> aad: bytes{length aad <= max_size_t /\ (length m + length aad) / Spec.Chacha20.blocklen <= max_size_t} ->
  Tot (lbytes (length m + Poly.size_block))

let aead_encrypt k n m aad =
  let len = length m in
  let len_aad : size_nat = length aad in
  let key0 = Spec.Chacha20.chacha20_key_block0 k n in
  let poly_k = sub key0 0 32 in
  let res = create (len + Poly.size_block) (u8 0) in
  let cipher = Spec.Chacha20.chacha20_encrypt_bytes k n 1 m in
  let mac = poly1305_do poly_k len cipher len_aad aad in
  let res = update_sub res 0 len cipher in
  let res = update_sub res len Poly.size_block mac in
  res


val aead_decrypt:
    k: key
  -> n: nonce
  -> c: bytes{length c + size_block <= max_size_t}
  -> mac: tag
  -> aad: bytes{length aad <= max_size_t /\ (length c + length aad) / 64 <= max_size_t} ->
  Tot (option (lbytes (length c)))

let aead_decrypt k n cipher mac aad =
  let len_aad = length aad in
  let clen = length cipher in
  let key0 = Spec.Chacha20.chacha20_key_block0 k n in
  let poly_k = sub key0 0 32 in
  let computed_mac = poly1305_do poly_k clen cipher len_aad aad in
  if lbytes_eq computed_mac mac then
    let plain = Spec.Chacha20.chacha20_encrypt_bytes k n 1 cipher in
    Some plain
  else None
