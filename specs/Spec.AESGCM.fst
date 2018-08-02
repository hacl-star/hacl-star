module Spec.AESGCM

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence

module AES = Spec.AES
module GF = Spec.GF128

(* Constants *)
let size_key: size_nat = 16
let size_nonce_ietf: size_nat = 12
let size_block: size_nat = 16

(* Types *)
type key = lbytes size_key



val ghash_:
    gmul_in_len:size_nat
  -> gmul_in:lbytes gmul_in_len
  -> tag_k:GF.key
  -> k:GF.key ->
  Tot GF.tag

let ghash_ gmul_in_len gmul_in tag_k k =
  let b0: GF.tag = AES.aes128_encrypt_block k (create size_block (u8 0)) in
  let h:lbytes size_block = GF.gmac gmul_in_len gmul_in b0 tag_k in
  h


val ghash:
    text_len:size_nat
  -> text:lbytes text_len
  -> aad_len:size_nat
  -> aad:lbytes aad_len
  -> tag_k:GF.key
  -> k:GF.key ->
  Tot GF.tag

let ghash text_len text aad_len aad tag_k k =
  (* gmul input: A || 0^v || C || 0^u || ceil(len(A))_64 || ceil(len(C))_64 *)
  let aad_padding = (size_block - (aad_len % size_block)) % size_block in
  let text_padding = (size_block - (text_len % size_block)) % size_block in
  let gmul_input_len: size_nat = aad_len + aad_padding + text_len + text_padding + size_block in
  let gmul_input = create gmul_input_len (u8 0) in
  let gmul_input = update_slice gmul_input 0 aad_len aad  in
  let gmul_input = update_slice gmul_input (aad_len + aad_padding) (aad_len + aad_padding + text_len) text  in
  let aad_len_bytes = nat_to_bytes_be 8 (aad_len * 8) in
  let gmul_input = update_slice gmul_input (aad_len + aad_padding + text_len + text_padding) (aad_len + aad_padding + text_len + text_padding + 8) aad_len_bytes  in
  let text_len_bytes = nat_to_bytes_be 8 (text_len * 8) in
  let gmul_input = update_slice gmul_input (aad_len + aad_padding + text_len + text_padding + 8) (aad_len + aad_padding + text_len + text_padding + size_block) text_len_bytes  in
  ghash_ gmul_input_len gmul_input tag_k k


val gcm:
    k:key
  -> n_len:size_nat
  -> n:lbytes n_len
  -> m_len:size_nat
  -> m:lbytes m_len
  -> aad_len:size_nat
  -> aad:lbytes aad_len ->
  Tot Spec.GF128.tag

let gcm k n_len n m_len m aad_len aad =
  let tag_key = AES.aes128_encrypt_bytes k n_len n 1 size_block (create size_block (u8 0)) in
  let mac = ghash m_len m aad_len aad tag_key k in
  mac


val aead_encrypt:
    k:key
  -> n_len:size_nat
  -> n:lbytes n_len
  -> len:size_nat{len + size_block <= max_size_t}
  -> m:lbytes len
  -> aad_len:size_nat{(len + aad_len) / size_block <= max_size_t}
  -> aad:lbytes aad_len ->
  Tot (lbytes (len + size_block))

let aead_encrypt k n_len n len m aad_len aad =
  let iv_len = if n_len = 12 then 12 else size_block in
  let iv: lbytes iv_len = if n_len = 12 then n else (
    (* gmul input: IV || 0^(s+64) || ceil(len(IV))_64 *)
    let n_padding:size_nat = (size_block - (n_len % size_block)) % size_block in
    let n_padding = n_padding + 8 in
    let gmul_input_len = n_len + n_padding + 8 in
    let gmul_input = create gmul_input_len (u8 0) in
    let gmul_input = update_slice gmul_input 0 n_len n  in
    let n_len_bytes = nat_to_bytes_be 8 (n_len * 8) in
    let gmul_input = update_slice gmul_input (n_len + n_padding) (n_len + n_padding + 8) n_len_bytes  in
    ghash_ gmul_input_len gmul_input (create size_block (u8 0)) k
  ) in
  let c = AES.aes128_encrypt_bytes k iv_len iv 2 len m in
  let mac = gcm k iv_len iv len c aad_len aad in
  let result = create (len + size_block) (u8 0) in
  let result = update_slice result 0 len c in
  let result = update_slice result len (len + size_block) mac in
  result


val aead_decrypt:
    k:key
  -> n_len:size_nat
  -> n:lbytes n_len
  -> clen:size_nat{size_block <= clen}
  -> c:lbytes clen
  -> aad_len:size_nat{(clen - size_block + aad_len) / size_block <= max_size_t}
  -> aad:lbytes aad_len ->
  Tot (lbytes (clen - size_block))

let aead_decrypt k n_len n clen c aad_len aad =
  let iv_len = if n_len = 12 then 12 else size_block in
  let iv: lbytes iv_len = if n_len = 12 then n else (
    let n_padding:size_nat = (size_block - (n_len % size_block)) % size_block in
    let n_padding = n_padding + 8 in
    let gmul_input_len = n_len + n_padding + 8 in
    let gmul_input = create gmul_input_len (u8 0) in
    let gmul_input = update_slice gmul_input 0 n_len n  in
    let n_len_bytes = nat_to_bytes_be 8 (n_len * 8) in
    let gmul_input = update_slice gmul_input (n_len + n_padding) (n_len + n_padding + 8) n_len_bytes  in
    ghash_ gmul_input_len gmul_input (create size_block (u8 0)) k
  ) in
  let encrypted_plaintext = sub c 0 (clen - size_block) in
  let associated_mac = sub c (clen - size_block) size_block in
  let computed_mac = gcm k iv_len iv (clen - size_block) encrypted_plaintext aad_len aad in
  let result = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) computed_mac associated_mac in
  let zeros = create (clen - size_block) (u8 0) in
  if result then
    AES.aes128_encrypt_bytes k iv_len iv 2 (clen - size_block) encrypted_plaintext
  else zeros
