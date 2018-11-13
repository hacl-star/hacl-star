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


val cbc_encrypt_last: iv -> key -> input:bytes{length input < size_block} -> FStar.All.ML block
let cbc_encrypt_last iv key input =
  let len = length input in
  let block = create size_block (u8 (size_block - len)) in
  let block = update_sub block 0 len input in
  let res = cbc_encrypt_block iv key block in
  IO.print_string "\nencrypt_last (block): \n";
  List.iter (fun a -> IO.print_uint8 (u8_to_UInt8 a);  IO.print_string ":") (to_list block);
  IO.print_string "\n";
  res


val unpadPKCS: block -> idx:size_nat{idx < size_block} -> Tot (option bytes)
let rec unpadPKCS b idx =
  let last_byte = b.[size_block - 1] in
  let vpad = uint_v last_byte in
  if vpad <= size_block then
    if (size_block - vpad) < idx then (
      if uint_v b.[idx] = uint_v last_byte then unpadPKCS b (idx - 1) else None)
    else (
      let plaintext = sub #uint8 #size_block b 0 (size_block - vpad) in
      Some plaintext)
  else None

val cbc_decrypt_last: iv -> key -> block -> FStar.All.ML (option bytes)
let cbc_decrypt_last iv k b =
  let plain_block = cbc_decrypt_block iv k b in
  IO.print_string "\ndecrypt_last (block): \n";
  List.iter (fun a -> IO.print_uint8 (u8_to_UInt8 a);  IO.print_string ":") (to_list plain_block);
  IO.print_string "\n";
  unpadPKCS plain_block (size_block - 1)


val aes128_cbc_encrypt:
    input: bytes{length input + size_block <= max_size_t}
  -> k: key
  -> iv: iv ->
  FStar.All.ML (ciphertext:bytes)

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
    let last_cipher_block = cbc_encrypt_last last_iv k last in
    ciphertext @| last_cipher_block)
  else (
    let padding = create size_block (u8 size_block) in
    let last_cipher_block = cbc_encrypt_block last_iv k padding in
    ciphertext @| last_cipher_block)


val aes128_cbc_decrypt:
    input: bytes{size_block <= length input
               /\ length input % size_block == 0
               /\ length input <= max_size_t}
  -> k: key
  -> iv: iv ->
  FStar.All.ML (option bytes)

let aes128_cbc_decrypt ciphertext k iv =
  let clen : size_nat = length ciphertext in
  let n : size_nat = clen / size_block in
  let last_iv, plaintext = generate_blocks size_block (n - 1) (fun _ -> block) (fun i iv ->
    let cblock_i = sub #uint8 #clen ciphertext (i * size_block) size_block in
    let plain_block = cbc_decrypt_block iv k cblock_i in
    cblock_i, plain_block) iv in
  IO.print_string "\nComputed plaintext (blocks): \n";
  List.iter (fun a -> IO.print_uint8 (u8_to_UInt8 a);  IO.print_string ":") (to_list plaintext);
  IO.print_string "\n";
let last_cipher_block = sub #uint8 #clen ciphertext ((n - 1) * size_block) size_block in
  match cbc_decrypt_last last_iv k last_cipher_block with
  | None -> None
  | Some last_plain_block ->
    Some (Seq.Base.append plaintext last_plain_block)
