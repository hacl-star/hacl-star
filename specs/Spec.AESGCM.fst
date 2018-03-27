module Spec.AESGCM

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes
open Spec.Lib.IntSeq

module AES = Spec.AES
module GF = Spec.GF128

let keylen: size_nat =   16
let blocksize: size_nat = 16

type key = lbytes keylen
type bytes = s:seq UInt8.t{length s < pow2 32}

(* TODO: rewrite with append *)

val ghash:
  text_len:size_nat ->
  text:lbytes text_len ->
  aad_len:size_nat ->
  aad:lbytes aad_len ->
  tag_k:GF.key ->
  k:GF.key ->
  Tot GF.tag
let ghash text_len text aad_len aad tag_k k =
  (* gmul input: A || 0^v || C || 0^u || ceil(len(A))_64 || ceil(len(C))_64 *)
  let aad_padding:size_nat = (16 - (aad_len % 16)) % 16 in
  let text_padding:size_nat = (16 - (text_len % 16)) % 16 in
  (* Build ghash input *)
  let gmul_input_len = aad_len + aad_padding + text_len + text_padding + blocksize in
  let gmul_input = create gmul_input_len (u8 0) in
  let gmul_input = update_slice gmul_input 0 aad_len aad  in
  (* padding is 0, so just skip those bytes *)
  let gmul_input = update_slice gmul_input (aad_len + aad_padding) (aad_len + aad_padding + text_len) text  in
  (* padding is 0, so just skip those bytes *)
  let aad_len_bytes = nat_to_bytes_be 8 (aad_len * 8) in
  let gmul_input = update_slice gmul_input (aad_len + aad_padding + text_len + text_padding) (aad_len + aad_padding + text_len + text_padding + 8) aad_len_bytes  in
  let text_len_bytes = nat_to_bytes_be 8 (text_len * 8) in
  let gmul_input = update_slice gmul_input (aad_len + aad_padding + text_len + text_padding + 8) (aad_len + aad_padding + text_len + text_padding + 16) text_len_bytes  in
  let b0: GF.tag = AES.aes128_encrypt_block k (create 16 0uy) in
  let h = GF.gmac gmul_input_len gmul_input b0 tag_k in
  h

val gcm:
  k:key ->
  n_len:size_nat ->
  n:lbytes n_len ->
  m_len:size_nat ->
  m:lbytes m_len ->
  aad_len:size_nat ->
  aad:lbytes aad_len ->
  Tot Spec.GF128.tag
let gcm k n_len n m_len m aad_len aad =
  let tag_key = AES.aes128_encrypt_bytes k n_len n 1 blocksize (create 16 0uy) in
  let mac = ghash m_len m aad_len aad tag_key k in
  mac

val aead_encrypt:
  k:key ->
  n_len:size_nat ->
  n:lbytes n_len ->
  len:size_nat{len + blocksize <= max_size_t} ->
  m:lbytes len ->
  aad_len:size_nat{(len + aad_len) / blocksize <= max_size_t} ->
  aad:lbytes aad_len ->
  Tot (lbytes (len + blocksize))
let aead_encrypt k n_len n len m aad_len aad =
  let iv = if n_len = 12 then n else (
    ghash n_len n (creat 0 0) 0 (create 16 0uy) k
  ) in
  let c = AES.aes128_encrypt_bytes k n_len n 2 len m in
  let mac = gcm k n_len n len c aad_len aad in
  let result = create (len + blocksize) (u8 0) in
  let result = update_slice result 0 len c in
  let result = update_slice result len (len + blocksize) mac in
  result
