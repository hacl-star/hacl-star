module Spec.AESGCM

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes
open Spec.Lib.IntSeq
open Spec.GaloisField

module AES = Spec.AES
module GF = Spec.GF128

#set-options "--z3rlimit 150 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

let keylen: size_nat =   16
let blocksize: size_nat = 16

type key = lbytes keylen
type bytes = s:seq UInt8.t{length s < pow2 32}

val ghash_:
  gmul_in_len:size_nat ->
  gmul_in:lbytes gmul_in_len ->
  tag_k:GF.key ->
  k:GF.key ->
  Tot GF.tag
let ghash_ gmul_in_len gmul_in tag_k k =
  let b0: GF.tag = AES.aes128_encrypt_block k (create blocksize (u8 0)) in
  let h:lbytes blocksize = GF.gmac gmul_in_len gmul_in b0 tag_k in
  h

val ghash:
  text_len:size_nat ->
  text:lbytes text_len ->
  aad_len:size_nat{aad_len + text_len + 3*blocksize <= max_size_t} ->
  aad:lbytes aad_len ->
  tag_k:GF.key ->
  k:GF.key ->
  Tot GF.tag
let ghash text_len text aad_len aad tag_k k =
  (* gmul input: A || 0^v || C || 0^u || ceil(len(A))_64 || ceil(len(C))_64 *)
  (* TODO: rewrite with concat *)
  let aad_padding:size_nat = (blocksize - (aad_len % blocksize)) % blocksize in
  let text_padding:size_nat = (blocksize - (text_len % blocksize)) % blocksize in
  let gmul_input_len:size_nat = aad_len + aad_padding + text_len + text_padding + blocksize in
  let gmul_input = create gmul_input_len (u8 0) in
  let gmul_input = update_slice gmul_input 0 aad_len aad  in
  let gmul_input = update_slice gmul_input (aad_len + aad_padding) (aad_len + aad_padding + text_len) text  in
  let aad_len_bytes = nat_to_bytes_be 8 (aad_len * 8) in
  let gmul_input = update_slice gmul_input (aad_len + aad_padding + text_len + text_padding) (aad_len + aad_padding + text_len + text_padding + 8) aad_len_bytes  in
  let text_len_bytes = nat_to_bytes_be 8 (text_len * 8) in
  let gmul_input = update_slice gmul_input (aad_len + aad_padding + text_len + text_padding + 8) (aad_len + aad_padding + text_len + text_padding + blocksize) text_len_bytes  in
  ghash_ gmul_input_len gmul_input tag_k k

val gcm:
  k:key ->
  n_len:size_nat ->
  n:lbytes n_len ->
  m_len:size_nat ->
  m:lbytes m_len ->
  aad_len:size_nat{(aad_len + m_len + 3*blocksize) <= max_size_t} ->
  aad:lbytes aad_len ->
  Tot Spec.GF128.tag
let gcm k n_len n m_len m aad_len aad =
  let tag_key = AES.aes128_encrypt_bytes k n_len n 1 blocksize (create blocksize (u8 0)) in
  let mac = ghash m_len m aad_len aad tag_key k in
  mac

val aead_encrypt:
  k:key ->
  n_len:size_nat{n_len + 2*blocksize <= max_size_t} ->
  n:lbytes n_len ->
  len:size_nat{len + blocksize <= max_size_t} ->
  m:lbytes len ->
  aad_len:size_nat{(aad_len + len + 3*blocksize) <= max_size_t} ->
  aad:lbytes aad_len ->
  Tot (lbytes (len + blocksize))
let aead_encrypt k n_len n len m aad_len aad =
  let iv_len = if n_len = 12 then 12 else blocksize in
  let iv: lbytes iv_len = if n_len = 12 then n else (
    (* gmul input: IV || 0^(s+64) || ceil(len(IV))_64 *)
    (* TODO: rewrite with concat *)
    let n_padding:size_nat = (blocksize - (n_len % blocksize)) % blocksize in
    let n_padding:size_nat = n_padding + 8 in
    let gmul_input_len:size_nat = n_len + n_padding + 8 in
    let gmul_input = create gmul_input_len (u8 0) in
    let gmul_input = update_slice gmul_input 0 n_len n  in
    let n_len_bytes = nat_to_bytes_be 8 (n_len * 8) in
    let gmul_input = update_slice gmul_input (n_len + n_padding) (n_len + n_padding + 8) n_len_bytes  in
    ghash_ gmul_input_len gmul_input (create blocksize (u8 0)) k
  ) in
  let c = AES.aes128_encrypt_bytes k iv_len iv 2 len m in
  let mac = gcm k iv_len iv len c aad_len aad in
  let result = create (len + blocksize) (u8 0) in
  let result = update_sub result 0 len c in
  let result = update_sub result len blocksize mac in
  result
