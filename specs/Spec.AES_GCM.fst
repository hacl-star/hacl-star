module Spec.AES_GCM

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators

module AES = Spec.AES
module GF = Spec.GF128

#set-options "--z3rlimit 25 --max_fuel 1"

(* Constants *)
let size_key (v:AES.variant) : size_nat = AES.key_size v
let size_block: size_nat = 16
let size_nonce: size_nat = 12
let size_tag: size_nat = size_block

(* Types *)
type key (v:AES.variant) = lbytes (size_key v)
type nonce = lbytes size_nonce
type tag = lbytes size_tag


inline_for_extraction
let padlen (x:nat) = ((size_block - x % size_block) % size_block)


val ghash:
    text: bytes{length text * 8 < pow2 64}
  -> aad: bytes{length aad * 8 < pow2 64}
  -> gf_key: GF.key
  -> tag_key: GF.key ->
  Tot GF.tag

let ghash text aad gf_key tag_key =
  (* gmul input: A || 0^v || C || 0^u || ceil(len(A))_64 || ceil(len(C))_64 *)
  let alen = length aad in
  let tlen = length text in
  let aad_pad = create (padlen alen) (u8 0) in
  let text_pad = create (padlen tlen) (u8 0) in
  let aad_len_bytes : lseq uint8 8 = nat_to_bytes_be 8 (alen * 8) in
  let text_len_bytes : lseq uint8 8 = nat_to_bytes_be 8 (tlen * 8) in
  let acc, r = GF.gf128_init gf_key in
  let acc = GF.gf128_update (Seq.append aad aad_pad) acc r in
  let acc = GF.gf128_update (Seq.append text text_pad) acc r in
  let acc = GF.gf128_update (Seq.append aad_len_bytes text_len_bytes) acc r in
  let tag = GF.gf128_finish tag_key acc in
  tag


val aead_init:
    v: AES.variant
  -> k: key v
  -> n: nonce
  -> Tot (AES.aes_ctr_state v & GF.key & GF.key)

let aead_init v k n =
  let st = AES.aes_ctr_init v k size_nonce n 0 in
  let gf_key = AES.aes_ctr_current_key_block v st in
  let st = AES.aes_ctr_add_counter v st 1 in
  let tag_key = AES.aes_ctr_current_key_block v st in
  let st = AES.aes_ctr_add_counter v st 1 in
  (st, gf_key, tag_key)

val aead_encrypt:
    v: AES.variant
  -> k: key v
  -> n: nonce
  -> m: bytes{length m * 8 < pow2 64 /\ length m / 16 <= max_size_t}
  -> aad: bytes {length aad * 8 < pow2 64} ->
  Tot (b:bytes{length b = length m + size_block})

let aead_encrypt v k n m aad =
  let mlen = length m in
  let (st,gf_key,tag_key) = aead_init v k n in
  let c  = AES.aes_ctr_encrypt_stream v st m in
  let mac = ghash c aad gf_key tag_key in
  Seq.append c mac

val aead_decrypt:
    v: AES.variant
  -> k: key v
  -> n: nonce
  -> aad:bytes{length aad * 8 < pow2 64}
  -> c: bytes{length c * 8 < pow2 64  /\ length c / 16 <= max_size_t}
  -> mac:tag
  -> Tot (option (b:bytes{length b = length c}))

let aead_decrypt v k n aad c tag =
  let clen = length c in
  let (st,gf_key,tag_key) = aead_init v k n in
  let computed_tag = ghash c aad gf_key tag_key in
  if lbytes_eq computed_tag tag then
    Some (AES.aes_ctr_encrypt_stream v st c)
  else None

let aes128gcm_encrypt k n m aad = aead_encrypt AES.AES128 k n m aad
let aes128gcm_decrypt k n aad c tag = aead_decrypt AES.AES128 k n aad c tag
let aes256gcm_encrypt k n m aad = aead_encrypt AES.AES256 k n m aad
let aes256gcm_decrypt k n aad c tag = aead_decrypt AES.AES256 k n aad c tag
