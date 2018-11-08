module Spec.AES128_CBC

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators

module AES = Spec.AES

(* Constants *)
let size_key: size_nat = 16
let size_block: size_nat = 16
let size_iv: size_nat = size_block

type key = lbytes size_key
type block = lbytes size_block
type iv = lbytes size_iv


val cbc_encrypt_block: iv -> key -> block -> Tot block
let cbc_encrypt_block iv key block =
  let aes_input = map2 (^.) iv block in
  AES.aes128_encrypt_block key aes_input


val cbc_decrypt_block: iv -> key -> block -> Tot block
let cbc_decrypt_block iv key block =
  let aes_output = AES.aes128_encrypt_block key block in
  map2 (^.) iv aes_output


val cbc_encrypt_last: iv -> key -> input:bytes{length input < size_block} -> Tot block
let cbc_encrypt_last iv key input =
  let len = length input in
  let block = create size_block (u8 (size_block - len)) in
  let block = update_sub block 0 len input in
  cbc_encrypt_block iv key block


val aes128_cbc_encrypt:
    input: bytes{length input * size_block <= max_size_t}
  -> k: key
  -> iv: iv ->
  Tot (ciphertext:bytes)

let aes128_cbc_encrypt input k iv =
  let len = length input in
  let n = len / size_block in
  let rem = len % size_block in
  let last_iv, ciphertext = generate_blocks size_block n (fun _ -> block) (fun i iv ->
    let block_i = sub #uint8 #len input (i * size_block) size_block in
    let cipher_block = cbc_encrypt_block iv k block_i in
    cipher_block, cipher_block) iv in
  if rem <> 0 then (
    let last = sub #uint8 #len input (n * size_block) rem in
    ciphertext @| (cbc_encrypt_last last_iv k last))
  else (
    let padding = create size_block (u8 size_block) in
    let last_cipher_block = cbc_encrypt_block last_iv k padding in
    ciphertext @| last_cipher_block)


val aes128_cbc_decrypt:
    input: bytes{length input % size_block == 0}
  -> k: key
  -> iv: iv ->
  Tot (option bytes)

let aes128_cbc_decrypt ciphertext k iv =
  let clen = length ciphertext in
  let n = clen / size_block in
  let _, plaintext = generate_blocks size_block n (fun _ -> block) (fun i iv ->
    let cblock_i = sub #uint8 #clen ciphertext (i * size_block) size_block in
    let plain_block = cbc_decrypt_block iv k cblock_i in
    cblock_i, plain_block) iv in
  let last_byte = plaintext.[clen - 1] in
  if last_byte > size_block then None
  else if plaintext.[clen - las]
