module Spec.AESGCM

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators

module AES = Spec.AES
module GF = Spec.GF128

(* Constants *)
let keylen: size_nat =   16
let blocksize: size_nat = 16

(* Types *)
type key = lbytes keylen

inline_for_extraction
let padlen (x:size_nat) = ((blocksize - x % blocksize) % blocksize)

val ghash:
    text_len:size_nat{text_len + padlen text_len <= max_size_t}
  -> text:lbytes text_len
  -> aad_len:size_nat{aad_len + padlen aad_len <= max_size_t}
  -> aad:lbytes aad_len
  -> gf_key:GF.key
  -> tag_key:GF.key ->
  Tot GF.tag

let ghash text_len text aad_len aad gf_key tag_key =
  (* gmul input: A || 0^v || C || 0^u || ceil(len(A))_64 || ceil(len(C))_64 *)
  let aad_pad = create (padlen aad_len) (u8 0) in
  let text_pad = create (padlen text_len) (u8 0) in
  let aad_len_bytes : lseq uint8 8 = nat_to_bytes_be 8 (aad_len * 8) in
  let text_len_bytes : lseq uint8 8 = nat_to_bytes_be 8 (text_len * 8) in
  let st = GF.init gf_key in
  let st = GF.poly (aad @| aad_pad) st in
  let st = GF.poly (text @| text_pad) st in
  let st = GF.poly (aad_len_bytes @| text_len_bytes) st in
  let tag = GF.finish st tag_key in
  tag

val gcm:
    k:key
  -> n_len:size_nat{n_len <= 12}
  -> n:lbytes n_len
  -> m_len:size_nat{m_len + padlen m_len <= max_size_t}
  -> m:lbytes m_len
  -> aad_len:size_nat{aad_len + padlen aad_len <= max_size_t}
  -> aad:lbytes aad_len ->
  Tot Spec.GF128.tag

#set-options "--z3rlimit 50"
let gcm k n_len n m_len m aad_len aad =
  let tag_key = AES.aes_key_block1 k n_len n in
  let gf_key = AES.aes_key_block0 k 12 (create 12 (u8 0)) in
  let mac = ghash m_len m aad_len aad gf_key tag_key in
  mac


val aead_encrypt:
    k:key
  -> n_len:size_nat{n_len == 12}
  -> n:lbytes n_len
  -> len:size_nat{len + padlen len <= max_size_t /\ len + blocksize <= max_size_t}
  -> m:lbytes len
  -> aad_len:size_nat{aad_len + padlen aad_len <= max_size_t}
  -> aad:lbytes aad_len ->
  Tot (lbytes (len + blocksize))

#reset-options "--z3rlimit 50"
let aead_encrypt k n_len n len m aad_len aad =
  let iv_len = 12 in
  let iv = create 12 (u8 0) in
  let iv = update_sub iv 0 n_len n in

  let c = AES.aes128_encrypt_bytes k iv_len iv 2 m in
  let mac = gcm k iv_len iv len c aad_len aad in
  let result = create (len + blocksize) (u8 0) in
  let result = update_slice result 0 len c in
  let result = update_slice result len (len + blocksize) mac in
  result


val aead_decrypt:
    k:key
  -> n_len:size_nat{n_len == 12}
  -> n:lbytes n_len
  -> clen:size_nat{blocksize <= clen}
  -> c:lbytes clen
  -> aad_len:size_nat{aad_len + padlen aad_len <= max_size_t}
  -> aad:lbytes aad_len ->
  Tot (lbytes (clen - blocksize))

let aead_decrypt k n_len n clen c aad_len aad =
  let iv_len = 12 in
  let iv = create 12 (u8 0) in
  let iv = update_sub iv 0 n_len n in
  let encrypted_plaintext = sub c 0 (clen - blocksize) in
  let associated_mac = sub c (clen - blocksize) blocksize in
  let computed_mac = gcm k iv_len iv (clen - blocksize) encrypted_plaintext aad_len aad in
  let result = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) computed_mac associated_mac in
  let zeros = create (clen - blocksize) (u8 0) in
  if result then
    AES.aes128_encrypt_bytes k iv_len iv 2 encrypted_plaintext
  else zeros
