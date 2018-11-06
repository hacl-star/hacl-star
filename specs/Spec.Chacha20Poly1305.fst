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
let size_block : size_nat = Poly.blocksize
let size_tag : size_nat = size_block

/// Types

type key = lbytes size_key
type nonce = lbytes size_nonce

/// Specification

let poly1305_padded (len:size_nat) (text:lbytes len) (tmp:lbytes Poly.blocksize) (st:Poly1305.state) : Tot (Poly1305.state) =
  let n = len / Poly.blocksize in
  let r = len % Poly.blocksize in
  let blocks = sub text 0 (n * Poly.blocksize) in
  let rem = sub text (n * Poly.blocksize) r in
  let st = Poly.poly blocks st in
  let tmp = update_sub tmp 0 r rem in
  let st = Poly1305.update1 Poly1305.blocksize tmp st in
  st

let poly1305_do
  (k:Poly.key)
  (len:size_nat{len <= max_size_t})
  (m:lbytes len)
  (aad_len:size_nat{(len + aad_len) / Spec.Chacha20.blocklen <= max_size_t})
  (aad:lbytes aad_len):
  Tot Poly.tag =

  let st = Poly.poly1305_init k in
  let block = create Poly.blocksize (u8 0) in
  let st = poly1305_padded aad_len aad block st in
  let st = poly1305_padded len m block st in
  let aad_len8 = uint_to_bytes_le #U64 (u64 aad_len) in
  let ciphertext_len8 = uint_to_bytes_le #U64 (u64 len) in
  let block = update_sub block 0 8 aad_len8 in
  let block = update_sub block 8 8 ciphertext_len8 in
  let st = Poly.update1 16 block st in
  Poly.finish st


val aead_encrypt:
    k:key
  -> n:nonce
  -> m: bytes{length m + size_block <= max_size_t}
  -> aad: bytes{length aad <= max_size_t /\ (length m + length aad) / Spec.Chacha20.blocklen <= max_size_t} ->
  Tot (lbytes (length m + Poly.blocksize))

let aead_encrypt k n m aad =
  let len = length m in
  let len_aad : size_nat = length aad in
  let key0 = Spec.Chacha20.chacha20_key_block0 k n in
  let poly_k = sub key0 0 32 in
  let res = create (len + Poly.blocksize) (u8 0) in
  let cipher = Spec.Chacha20.chacha20_encrypt_bytes k n 1 m in
  let mac = poly1305_do poly_k len cipher len_aad aad in
  let res = update_sub res 0 len cipher in
  let res = update_sub res len Poly.blocksize mac in
  res


val aead_decrypt:
    k: key
  -> n: nonce
  -> c: bytes{size_tag <= length c /\ length c <= max_size_t}
  -> aad: bytes{length aad <= max_size_t /\ (length c + length aad) / 64 <= max_size_t} ->
  Tot (option (lbytes (length c - size_block)))

let aead_decrypt k n c aad =
  let clen = length c in
  let len_aad = length aad in
  let nonce = create size_nonce (u8 0) in
  let nonce = update_sub nonce 0 size_nonce n in
  let encrypted_plaintext = sub #uint8 #clen c 0 (clen - size_block) in
  let provided_mac = sub #uint8 #clen c (clen - size_block) size_block in
  let key0 = Spec.Chacha20.chacha20_key_block0 k n in
  let poly_k = sub key0 0 32 in
  let computed_mac = poly1305_do poly_k (clen - size_block) encrypted_plaintext len_aad aad in
  let result = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) computed_mac provided_mac in
  if result then
    let plain = Spec.Chacha20.chacha20_encrypt_bytes k n 1 encrypted_plaintext in
    Some plain
  else None
